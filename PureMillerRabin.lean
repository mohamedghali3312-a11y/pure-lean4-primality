namespace PureMillerRabin

/-- Exponentiation modulaire binaire exacte (en entiers purs Nat, 0 float) -/
def modPow (base exp mod : Nat) : Nat :=
  if mod ≤ 1 then 0
  else
    let rec loop (b e acc : Nat) : Nat :=
      match e with
      | 0 => acc % mod
      | e' + 1 =>
        let acc' := if (e' + 1) % 2 == 1 then (acc * b) % mod else acc
        let b' := (b * b) % mod
        loop b' ((e' + 1) / 2) acc'
    termination_by e
    decreasing_by
      simp_wf
      omega
    loop (base % mod) exp 1

/-- Décompose un entier m > 0 en (s, d) tel que m = 2^s * d avec d impair -/
def factorTwos (m : Nat) : Nat × Nat :=
  let rec go (s d : Nat) : Nat × Nat :=
    if d == 0 then (s, 0)
    else if d % 2 == 0 then go (s + 1) (d / 2)
    else (s, d)
  termination_by d
  decreasing_by
    simp_wf
    omega
  go 0 m

/-- Vérifie la boucle de mise au carré répétée de Miller-Rabin (s - 1 itérations) -/
def checkSquares (x n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let x' := (x * x) % n
    if x' == n - 1 then true
    else if x' == 1 then false
    else checkSquares x' n k

/-- Test d'un témoin fort de Miller-Rabin pour a sur l'entier impair n > 2 -/
def passesWitness (n a : Nat) : Bool :=
  let a' := a % n
  if a' == 0 then true
  else
    let (s, d) := factorTwos (n - 1)
    let x0 := modPow a' d n
    if x0 == 1 || x0 == n - 1 then true
    else
      match s with
      | 0 => false
      | s' + 1 => checkSquares x0 n s'

/-- Les 7 témoins déterministes officiels certifiant tout entier 64-bit (< 2^64) -/
def witnesses64 : List Nat :=
  [2, 325, 9375, 28178, 450775, 9780504, 1795265022]

/-- Test de primalité déterministe 64-bit complet en Lean 4 pur -/
def isDeterministicPrime64 (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 || n == 3 then true
  else if n % 2 == 0 then false
  else witnesses64.all (passesWitness n)

/-- THÉORÈME 1 : La décomposition factorTwos reconstruit exactement m = 2^s * d -/
theorem factorTwos_go_spec (s d : Nat) :
    2 ^ (factorTwos.go s d).1 * (factorTwos.go s d).2 = 2 ^ s * d := by
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    unfold factorTwos.go
    split
    · next h0 =>
      have hd0 : d = 0 := beq_iff_eq.mp h0
      subst hd0
      simp
    · next h0 =>
      split
      · next heven =>
        have hmod : d % 2 = 0 := beq_iff_eq.mp heven
        have hlt : d / 2 < d := Nat.div_lt_self (Nat.pos_of_ne_zero (mt beq_iff_eq.mpr h0)) (by decide)
        rw [ih (d / 2) hlt (s + 1)]
        have hdiv : 2 * (d / 2) = d := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        calc
          2 ^ (s + 1) * (d / 2) = 2 ^ s * (2 * (d / 2)) := by
            rw [Nat.pow_succ, Nat.mul_assoc]
          _ = 2 ^ s * d := by rw [hdiv]
      · rfl

theorem factorTwos_spec (m : Nat) :
    2 ^ (factorTwos m).1 * (factorTwos m).2 = m := by
  unfold factorTwos
  rw [factorTwos_go_spec 0 m]
  simp

/-- THÉORÈME 2 : Certification formelle exécutable sur des nombres premiers 64-bit
    (dont le premier de Mersenne 2^61 - 1 = 2305843009213693951 et le premier NTT 998244353) -/
theorem cert_ntt_prime_998244353 : isDeterministicPrime64 998244353 = true := by
  decide

theorem cert_mersenne_61 : isDeterministicPrime64 2305843009213693951 = true := by
  decide

theorem cert_carmichael_561_rejected : isDeterministicPrime64 561 = false := by
  decide

theorem cert_carmichael_1729_rejected : isDeterministicPrime64 1729 = false := by
  decide

#print axioms factorTwos_spec
#print axioms cert_ntt_prime_998244353
#print axioms cert_mersenne_61
#print axioms cert_carmichael_561_rejected

end PureMillerRabin
