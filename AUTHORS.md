# Authors

- Mate Soos, Argot Collective

## Acknowledgement

This project is inspired by and builds on the ideas of
[GASOL](https://github.com/costa-group/gasol-optimizer), the EVM superoptimizer by
**Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio and Maria A. Schett**
(COSTA group). The stack functional specification (SFS) representation of a block, the
simplification rules and the overall approach (lift a block, simplify, re-synthesise cheaper
code) come from their work:

- Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio.
  [*A Max-SMT Superoptimizer for EVM handling Memory and Storage*](https://doi.org/10.1007/978-3-030-99524-9_11).
  TACAS 2022, LNCS 13243, Springer.
- Elvira Albert, Pablo Gordillo, Alejandro Hernández-Cerezo, Albert Rubio, Maria A. Schett.
  [*Super-Optimization of Smart Contracts*](https://doi.org/10.1145/3506800).
  ACM Transactions on Software Engineering and Methodology 31(4), 2022.

The correctness proofs are against powdr-labs'
[evm-semantics](https://github.com/powdr-labs/evm-semantics), a formal EVM semantics in Lean 4,
which in turn builds on Nethermind's [EVMYulLean](https://github.com/NethermindEth/EVMYulLean).
We thank both teams: without a precise, executable and conformance-tested model of the EVM,
proving the optimiser correct would not be possible.
