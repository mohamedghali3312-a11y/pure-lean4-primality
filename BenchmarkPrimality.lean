import PurePrimality

namespace PrimalityBenchmark
open PurePrimality

/-- Test 1 : Nombre premier de Proth classique p = 3 * 2^30 + 1 = 3 221 225 473 (témoin a = 5) -/
theorem proth_prime_3_2_30_certified :
    isProthWitness 5 (3 * 2 ^ 30 + 1) = true := by
  decide

/-- Test 2 : Nombre premier de Proth p = 15 * 2^27 + 1 = 2 013 265 921 (témoin a = 31) -/
theorem proth_prime_15_2_27_certified :
    isProthWitness 31 (15 * 2 ^ 27 + 1) = true := by
  decide

/-- Test 3 : Nombre premier de Proth NTT 64-bit p = 27 * 2^56 + 1 (témoin a = 3) -/
theorem proth_prime_64bit_certified :
    isProthWitness 3 (27 * 2 ^ 56 + 1) = true := by
  decide

/-- Test 4 : Rejet garanti d'un nombre composé de Fermat F_5 = 2^32 + 1 = 4 294 967 297 -/
theorem fermat_F5_composite_rejected :
    isProthWitness 3 (2 ^ 32 + 1) = false := by
  decide

/-- Test 5 : Cohérence exacte entre modPow rapide et la définition mathématique sur p = 65537 -/
theorem fermat_F4_modPow_exact :
    modPow 3 32768 65537 = 65536 := by
  decide

#print axioms proth_prime_3_2_30_certified
#print axioms proth_prime_64bit_certified
#print axioms fermat_F5_composite_rejected

end PrimalityBenchmark
