import PurePrimality

namespace PrimalityBenchmark
open PurePrimality

theorem proth_prime_769_certified :
    isProthWitness 11 (3 * 2 ^ 8 + 1) = true := by
  decide

theorem fermat_F3_257_certified :
    isProthWitness 3 (2 ^ 8 + 1) = true := by
  decide

theorem proth_composite_1281_rejected :
    isProthWitness 3 (5 * 2 ^ 8 + 1) = false := by
  decide

theorem fermat_F3_modPow_exact :
    modPow 3 128 257 = 256 := by
  decide

#eval isProthWitness 5 (3 * 2 ^ 30 + 1)
#eval isProthWitness 31 (15 * 2 ^ 27 + 1)
#eval isProthWitness 5 (27 * 2 ^ 56 + 1)
#eval isProthWitness 3 (2 ^ 32 + 1)

#print axioms proth_prime_769_certified
#print axioms fermat_F3_257_certified
#print axioms proth_composite_1281_rejected
#print axioms fermat_F3_modPow_exact

end PrimalityBenchmark
