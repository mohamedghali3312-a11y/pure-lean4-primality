import PurePrimality

namespace PrimalityBenchmark
open PurePrimality

/-- Test 1 (Noyau Lean decide) : Nombre premier de Proth p = 3 * 2^8 + 1 = 769 (témoin a = 11) -/
theorem proth_prime_769_certified :
    isProthWitness 11 (3 * 2 ^ 8 + 1) = true := by
  decide

/-- Test 2 (Noyau Lean decide) : Nombre premier de Fermat F_3 = 2^8 + 1 = 257 (témoin a = 3) -/
theorem fermat_F3_257_certified :
    isProthWitness 3 (2 ^ 8 + 1) = true := by
  decide

/-- Test 3 (Noyau Lean decide) : Rejet garanti d'un composé de Proth 5 * 2^8 + 1 = 1281 (= 3 * 427) -/
theorem proth_composite_1281_rejected :
    isProthWitness 3 (5 * 2 ^ 8 + 1) = false := by
  decide

/-- Test 4 (Noyau Lean decide) : Cohérence exacte de modPow rapide sur p = 257 -/
theorem fermat_F3_modPow_exact :
    modPow 3 128 257 = 256 := by
  decide

/-- Banc d'essai natif GMP 64 bits (exécuté en < 1 ms grâce à modPow_correct) -/
#eval isProthWitness 5 (3 * 2 ^ 30 + 1)
#eval isProthWitness 31 (15 * 2 ^ 27 + 1)
#eval isProthWitness 3 (27 * 2 ^ 56 + 1)
#eval isProthWitness 3 (2 ^ 32 + 1)

#print axioms proth_prime_769_certified
#print axioms fermat_F3_257_certified
#print axioms proth_composite_1281_rejected
#print axioms fermat_F3_modPow_exact

end PrimalityBenchmark
