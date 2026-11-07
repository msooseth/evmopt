import EvmOpt
import EvmOpt.Asm

open EvmOpt EvmSemantics EvmSemantics.EVM

def blk (s : String) : Block :=
  (parseBlock s).filterMap fun | .ins i => some i | .other _ => none

def opt (s : String) (f : Fork := .Cancun) : String :=
  " ".intercalate ((peephole f (blk s)).map Instr.show)

def ok (a b : String) (f : Fork := .Cancun) : Bool := check f (blk a) (blk b)

#guard opt "SWAP1 SWAP1" = ""
#guard opt "SWAP3 SWAP3 DUP1" = "DUP1"
#guard opt "DUP3 POP" = ""
#guard opt "PUSH1 0x05 POP" = ""
#guard opt "ADD POP" = "POP POP"
#guard opt "ADDMOD POP" = "POP POP POP"
#guard opt "PUSH1 0x05 PUSH1 0x03 ADD" = "PUSH1 0x08"
#guard opt "PUSH1 0x03 PUSH1 0x05 SUB" = "PUSH1 0x02"
-- folding to a PUSH32 would grow the code: kept
#guard opt "PUSH1 0x01 PUSH1 0x00 SUB" = "PUSH1 0x01 PUSH0 SUB"
#guard opt "PUSH1 0x07 PUSH1 0x05 PUSH1 0x03 ADDMOD" = "PUSH1 0x01"
#guard opt "PUSH1 0x00 ISZERO" = "PUSH1 0x01"
#guard opt "PUSH0 ADD" = ""
#guard opt "PUSH1 0x01 MUL" = ""
#guard opt "PUSH0 MUL" = "POP PUSH0"
#guard opt "PUSH0 SWAP1 SUB" = ""
#guard opt "PUSH1 0x01 SWAP1 DIV" = ""
#guard opt "DUP1 SUB" = "POP PUSH0"
#guard opt "DUP1 XOR" = "POP PUSH0"
-- saves 1 gas for 1 extra byte: rejected by the size policy
#guard opt "DUP1 EQ" = "DUP1 EQ"
#guard opt "DUP1 AND" = ""
#guard opt "SWAP1 ADD" = "ADD"
#guard opt "SWAP1 LT" = "GT"
#guard opt "SWAP1 SGT" = "SLT"
#guard opt "NOT NOT" = ""
#guard opt "ISZERO ISZERO ISZERO" = "ISZERO"
#guard opt "PUSH0 SHL" = ""
#guard opt "PUSH0 SHR" = ""
#guard opt "PUSH0 EQ" = "ISZERO"
#guard opt "PUSH1 0x01 SWAP1 LT" = "ISZERO"
#guard opt "PUSH1 0x01 GT" = "ISZERO"
#guard opt "PUSH0 SWAP1 LT" = "POP PUSH0"
#guard opt "PUSH0 GT" = "POP PUSH0"
#guard opt "PUSH2 0x0005" = "PUSH1 0x05"
#guard opt "PUSH1 0x00" = "PUSH0"
-- PUSH0 does not exist before Shanghai.
#guard opt "PUSH1 0x00" (f := .Berlin) = "PUSH1 0x00"
#guard opt "PUSH0 MUL" (f := .Berlin) = "PUSH0 MUL"
-- cascading: PUSH a PUSH b ADD then the folded constant feeds MUL by 1
#guard opt "PUSH1 0x02 PUSH1 0x03 ADD PUSH1 0x01 MUL" = "PUSH1 0x05"

-- gasol's claimed optimum for examples/blocks/redundant_swap.txt validates.
#guard ok "SWAP1 SWAP4 DUP5 SWAP2 SWAP1" "DUP2 SWAP5"
#guard !ok "SWAP1 SWAP4 DUP5 SWAP2 SWAP1" "DUP2 SWAP4"
-- gasol-bugs.md 1-3: the buggy rules' outputs are rejected, the correct ones accepted.
#guard !ok "DUP1 DIV" "POP PUSH1 0x01"
#guard !ok "PUSH0 SHL" "POP PUSH0"
#guard ok "PUSH0 SWAP1 SHL" "POP PUSH0"
#guard !ok "PUSH0 SWAP1 SHL" ""
-- candidates must not read deeper or cost more
#guard !ok "POP" "SWAP1 POP POP PUSH0 ADD"
#guard !ok "DUP1" "DUP2"
-- gasol outputs validated via absorption / cancellation rules
#guard ok "DUP2 DUP2 OR DUP3 OR" "DUP1 DUP3 OR"
#guard ok "DUP1 DUP3 XOR DUP3 XOR" "DUP1"
#guard ok "DUP2 DUP2 AND DUP3 OR" "DUP2 POP DUP2"
-- gasol-bugs.md A-D: gasol's wrong constant folds are rejected
#guard !ok "PUSH1 0x03 PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff DIV"
  "PUSH32 0x5555555555555400000000000000000000000000000000000000000000000000"
#guard !ok "PUSH1 0x03 PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff SMOD"
  "PUSH0"
#guard opt "PUSH1 0x03 PUSH32 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff DIV"
  = "PUSH32 0x" ++ String.join (List.replicate 32 "55")

def sopt (s : String) (f : Fork := .Cancun) : String :=
  " ".intercalate ((optimizeBlock f (blk s)).map Instr.show)

-- search (validated by check) finds gasol's optimum and removes dead computation
#guard sopt "SWAP1 SWAP4 DUP5 SWAP2 SWAP1" = "DUP2 SWAP5"
#guard sopt "DUP3 DUP3 ADD SWAP2 POP SWAP1 POP" = "SWAP1 POP"
#guard sopt "SWAP2 SWAP1 SWAP2 SWAP1" = "SWAP1 SWAP2"
#guard sopt "PUSH1 0x01 DUP2 ADD SWAP1 POP" = "PUSH1 0x01 ADD"
#guard sopt "DUP1 DUP3 XOR DUP3 XOR" = "DUP1"

-- env reads (gasol interesting_examples/caller_redundant_check.txt)
#guard sopt "CALLER PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND PUSH1 0x00" = "CALLER PUSH0"
#guard ok "CALLER PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND" "CALLER"
#guard !ok "CALLVALUE PUSH20 0xffffffffffffffffffffffffffffffffffffffff AND" "CALLVALUE"
#guard sopt "CALLER CALLER EQ" = "PUSH1 0x01"
#guard sopt "PUSH0 CALLDATALOAD DUP1 POP" = "PUSH0 CALLDATALOAD"

-- DUP of a known zero becomes PUSH0 (gasol corpus pattern)
#guard sopt "PUSH0 DUP1 PUSH1 0x40 DUP4 DUP6 SUB SLT ISZERO" = "PUSH0 PUSH0 PUSH1 0x40 DUP4 DUP6 SUB SLT ISZERO"
#guard sopt "PUSH0 DUP1 PUSH0 DUP1 PUSH1 0x80 DUP6 DUP8 SUB SLT ISZERO" = "PUSH0 PUSH0 PUSH0 PUSH0 PUSH1 0x80 DUP6 DUP8 SUB SLT ISZERO"
#guard sopt "PUSH1 0x00 DUP1" (f := .Berlin) = "PUSH1 0x00 DUP1"
-- greedy scheduler with CSE and solc-style constant recipes (gasol corpus block)
#guard sopt "DUP2 PUSH1 0x01 PUSH1 0x01 PUSH1 0xa0 SHL SUB AND DUP4 PUSH1 0x01 PUSH1 0x01 PUSH1 0xa0 SHL SUB AND EQ"
  = "PUSH1 0x01 DUP1 PUSH1 0xa0 SHL SUB DUP1 DUP5 AND SWAP1 DUP4 AND EQ"
-- the mask stays a short recipe (folding to PUSH20 would add 13 bytes); DUP1 saves a byte
#guard sopt "PUSH1 0x01 PUSH1 0x01 PUSH1 0xa0 SHL SUB" = "PUSH1 0x01 DUP1 PUSH1 0xa0 SHL SUB"
