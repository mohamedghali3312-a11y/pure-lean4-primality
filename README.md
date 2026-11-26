# Pure Lean 4 Primality, Euclid's Lemma & 64-Bit Proth Witness Certification

[![Pure Lean 4 CI](https://github.com)](https://github.com)
[![DOI](https://zenodo.org)](https://doi.org)
[![ORCID](https://shields.io)](https://orcid.org)

**Author:** Mohamed Ghali (`ORCID: 0009-0006-3364-5341`)  
**Software Priority Registration:** INPI e-Soleau Deposit No. `DSO2026046588` (France)

---

## Overview

This repository provides a **100% autonomous, zero-dependency formalization** (`0 Mathlib`, `0 sorryAx`) of elementary number theory, modular arithmetic invariants, fast binary modular exponentiation, and executable Proth primality witness verification in **Pure Lean 4**.

Every theorem is checked directly by the Lean 4 kernel without external libraries or unverified reduction axioms (`ofReduceBool`, `trustCompiler`, or `sorryAx`).

---

## Formally Verified Theorems (`PurePrimality.lean`)

1. **`exists_prime_factor`:** Every natural number $n \ge 2$ admits at least one prime divisor $p \mid n$.
2. **`euclid_lemma`:** Pure natural-number descent proof of Euclid's Lemma ($p \mid a \cdot b \implies p \mid a \lor p \mid b$) without requiring signed integers (`Int`) or Bézout's identity.
3. **`mod_cancel_left`:** Modular cancellation modulo a prime $p$ ($a \cdot x \equiv a \cdot y \pmod p \land p \nmid a \implies x \equiv y \pmod p$).
4. **`miller_rabin_sqrt_one`:** Characterization of modular square roots of unity ($x^2 \equiv 1 \pmod p \implies x \equiv \pm 1 \pmod p$).
5. **`modPow_correct`:** Exact functional equivalence between $\mathcal{O}(\log e)$ binary modular exponentiation `modPow a e m` and mathematical exponentiation $(a^e) \bmod m$.
6. **`isProthWitness`:** Executable kernel-decidable Proth witness check ($a^{(p-1)/2} \equiv p - 1 \pmod p$) supporting 64-bit NTT Proth primes such as $27 \cdot 2^{56} + 1$.

---

## Kernel & Native 64-Bit Benchmark (`BenchmarkPrimality.lean`)

* **Kernel-level `decide` proofs (`0` axioms):**
  * Proth prime $p = 3 \cdot 2^8 + 1 = 769$ certified (`a = 11`).
  * Fermat prime $F_3 = 2^8 + 1 = 257$ certified (`a = 3`).
  * Composite Proth candidate $5 \cdot 2^8 + 1 = 1281 = 3 \times 427$ deterministically rejected.
* **Native 64-bit NTT modulus verification (`#eval`):**
  * $p = 3 \cdot 2^{30} + 1 = 3\,221\,225\,473$ (`a = 5`) $\to$ `true`
  * $p = 15 \cdot 2^{27} + 1 = 2\,013\,265\,921$ (`a = 31`) $\to$ `true`
  * $p = 27 \cdot 2^{56} + 1 = 1\,945\,555\,039\,024\,054\,273$ (`a = 5`) $\to$ `true`
  * Composite Fermat number $F_5 = 2^{32} + 1 = 4\,294\,967\,297$ (`a = 3`) $\to$ `false`
