namespace PureMillerRabin

def powModLoop (mod : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc % mod
  | fuel + 1, b, e, acc =>
    if e == 0 then acc % mod
    else
      let acc' := if e % 2 == 1 then (acc * b) % mod else acc
      powModLoop mod fuel ((b * b) % mod) (e / 2) acc'

def modPow (base exp mod : Nat) : Nat :=
  if mod ≤ 1 then 0
  else powModLoop mod (exp + 1) (base % mod) exp 1

def factorTwosLoop : Nat → Nat → Nat → Nat × Nat
  | 0, s, d => (s, d)
  | fuel + 1, s, d =>
    if d == 0 then (s, 0)
    else if d % 2 == 0 then factorTwosLoop fuel (s + 1) (d / 2)
    else (s, d)

def factorTwos (m : Nat) : Nat × Nat :=
  factorTwosLoop m 0 m

def checkSquares (x n : Nat) : Nat → Bool
  | 0 => false
  | k + 1 =>
    let x' := (x * x) % n
    if x' == n - 1 then true
    else if x' == 1 then false
    else checkSquares x' n k

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

/-- Test déterministe complet 64-bit avec les 7 témoins officiels (Sinclair) -/
def isDeterministicPrime64 (n : Nat) : Bool :=
  if n < 2 then false
  else if n == 2 || n == 3 then true
  else if n % 2 == 0 then false
  else
    passesWitness n 2 &&
    passesWitness n 325 &&
    passesWitness n 9375 &&
    passesWitness n 28178 &&
    passesWitness n 450775 &&
    passesWitness n 9780504 &&
    passesWitness n 1795265022

theorem factorTwosLoop_spec : ∀ (fuel s d : Nat),
    2 ^ (factorTwosLoop fuel s d).1 * (factorTwosLoop fuel s d).2 = 2 ^ s * d
  | 0, s, d => rfl
  | fuel + 1, s, d => by
    unfold factorTwosLoop
    split
    · next h0 =>
      have hd0 : d = 0 := beq_iff_eq.mp h0
      subst hd0
      simp
    · next h0 =>
      split
      · next heven =>
        have hmod : d % 2 = 0 := beq_iff_eq.mp heven
        rw [factorTwosLoop_spec fuel (s + 1) (d / 2)]
        have hdiv : 2 * (d / 2) = d := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)
        calc
          2 ^ (s + 1) * (d / 2) = 2 ^ s * (2 * (d / 2)) := by
            rw [Nat.pow_succ, Nat.mul_assoc]
          _ = 2 ^ s * d := by rw [hdiv]
      · rfl

theorem factorTwos_spec (m : Nat) :
    2 ^ (factorTwos m).1 * (factorTwos m).2 = m := by
  unfold factorTwos
  rw [factorTwosLoop_spec m 0 m]
  simp

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
