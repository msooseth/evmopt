import EvmOpt
open EvmSemantics UInt256

-- gasol DIV(X,X) → 1 (gasol_optimization.py:4002): false at X = 0.
example : div (ofNat 0) (ofNat 0) ≠ ofNat 1 := by decide

-- gasol SHL(0,X) → inp_vars[0] = 0 (gasol_optimization.py:4140): shift 0 of X=1 is 1.
example : shiftLeft (ofNat 1) (ofNat 0) ≠ ofNat 0 := by decide
example : shiftRight (ofNat 1) (ofNat 0) ≠ ofNat 0 := by decide

-- gasol SHL(X,0) → inp_vars[0] = shift (gasol_optimization.py:4147): shifting value 0 by 5 is 0.
example : shiftLeft (ofNat 0) (ofNat 5) ≠ ofNat 5 := by decide
example : shiftRight (ofNat 0) (ofNat 5) ≠ ofNat 5 := by decide

-- gasol models SMOD as MOD (ir_block.py:240): SMOD(-1, 3) = -1 but MOD(2^256-1, 3) = 0.
example : smod (ofNat (2^256 - 1)) (ofNat 3) ≠ (ofNat (2^256 - 1)) % (ofNat 3) := by decide
