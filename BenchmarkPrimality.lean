import PurePrimality

namespace PrimalityBenchmark
open PurePrimality

/-- Test 1 : Nombre premier de Proth p = 3 * 2^12 + 1 = 12 289 (témoin a = 11) -/
theorem proth_prime_12289_certified :
    isProthWitness 11 (3 * 2 ^ 12 + 1) = true := by
  decide

/-- Test 2 : Nombre premier de Proth p = 5 * 2^13 + 1 = 40 961 (témoin a = 3) -/
theorem proth_prime_40961_certified :
    isProthWitness 3 (5 * 2 ^ 13 + 1) = true := by
  decide

/-- Test 3 : Nombre premier de Fermat F_4 = 2^16 + 1 = 65 537 (témoin a = 3) -/
theorem fermat_F4_65537_certified :
    isProthWitness 3 (2 ^ 16 + 1) = true := by
  decide

/-- Test 4 : Rejet garanti d'un nombre composé de Proth 3 * 2^10 + 1 = 3 073 (= 7 * 439) -/
theorem proth_composite_3073_rejected :
    isProthWitness 3 (3 * 2 ^ 10 + 1) = false := by
  decide

/-- Test 5 : Cohérence exacte entre modPow rapide et la définition mathématique sur p = 65537 -/
theorem fermat_F4_modPow_exact :
    modPow 3 32768 65537 = 65536 := by
  decide

#print axioms proth_prime_12289_certified
#print axioms proth_prime_40961_certified
#print axioms fermat_F4_65537_certified
#print axioms proth_composite_3073_rejected

end PrimalityBenchmark
