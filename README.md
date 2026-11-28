# Pure Lean 4 Primality & Number Theory Kernel

[![Pure Lean 4 Primality & Benchmark CI](https://github.com)](https://github.com)

A zero-dependency, formally verified number theory and 64-bit deterministic primality suite written in **Pure Lean 4** (`0 Mathlib`, `0 sorryAx`).

## Certified Modules & Theorems

| File | Mathematical Scope | Kernel Verification (`#print axioms`) |
| :--- | :--- | :--- |
| **`PurePrimality.lean`** | Full 64-bit deterministic primality engine & verified integer arithmetic primitives. | **0 external dependencies** (`0 sorryAx`) |
| **`PureFermat.lean`** | Complete constructive proof of **Fermat's Little Theorem** ($a^{p-1} \equiv 1 \pmod p$ for prime $p$ and $p \nmid a$). | **Standard Lean axioms only** (`0 sorryAx`) |
| **`PureMillerRabin.lean`** | Structural $2^s \cdot d$ decomposition (`factorTwos_spec`), strong witness verification (Sinclair 64-bit witness set), Mersenne prime $M_{31}$ certification, and formal rejection of Carmichael numbers (`561`, `1729`, `2821`). | **Kernel-reduced (`decide`) & pure Nat proofs** (`0 sorryAx`) |
| **`BenchmarkPrimality.lean`** | Continuous integration benchmark suite executed on every push. | **Automated CI Verified** |

## Why Zero-Dependency Pure Lean 4?

- **Minimal Trusted Computing Base (TCB):** Compiles directly against Lean 4's core standard library without importing heavy external libraries.
- **Deterministic & Exact:** Pure `Nat` / `UInt64` modular exponentiation (`modPow`) and binary decomposition with zero floating-point operations.
- **Cryptographic Readiness:** Designed for formal verification of NTT primes (`998244353`), Mersenne primes (`2147483647`), and post-quantum / FHE arithmetic pipelines.

## Author & Provenance

- **Author:** Mohamed Ghali — Formal Verification Engineer (Lean 4)
- **ORCID:** [0009-0006-3364-5341](https://orcid.org)
- **Intellectual Property:** Registered via **INPI e-Soleau (`DSO2026046588`)**
