namespace PurePrimality

def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

theorem dvd_sub_of_dvd {p x y : Nat} (hyx : y ≤ x) (hx : p ∣ x) (hy : p ∣ y) : p ∣ x - y := by
  rcases hx with ⟨kx, rfl⟩
  rcases hy with ⟨ky, rfl⟩
  refine ⟨kx - ky, ?_⟩
  exact (Nat.mul_sub_left_distrib p kx ky).symm

/-- 1. Existence d'un diviseur premier pour tout n ≥ 2 -/
theorem exists_prime_factor : ∀ n : Nat, 2 ≤ n → ∃ p : Nat, IsPrime p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hprime : ∀ d : Nat, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hprime⟩, Nat.dvd_refl n⟩
    · have hex : ∃ d : Nat, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by
        apply Classical.byContradiction
        intro hno
        apply hprime
        intro d hd
        by_cases h1 : d = 1
        · exact Or.inl h1
        · by_cases hn_eq : d = n
          · exact Or.inr hn_eq
          · exfalso; exact hno ⟨d, hd, h1, hn_eq⟩
      rcases hex with ⟨d, hd_dvd, hd_ne1, hd_nen⟩
      have hd_ge2 : 2 ≤ d := by
        have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
        omega
      have hd_lt : d < n := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hd_dvd) hd_nen
      rcases ih d hd_lt hd_ge2 with ⟨p, hp_prime, hp_dvd_d⟩
      exact ⟨p, hp_prime, Nat.dvd_trans hp_dvd_d hd_dvd⟩

/-- Lemme auxiliaire : si p ∣ x * b et p ∣ q * b, alors p ∣ (x % q) * b -/
theorem dvd_mod_mul_of_dvd {p q x b : Nat} (hq_pos : 0 < q)
    (hxb : p ∣ x * b) (hqb : p ∣ q * b) : p ∣ (x % q) * b := by
  have h_eq : q * (x / q) + x % q = x := Nat.div_add_mod x q
  have h_mul : q * (x / q) * b + (x % q) * b = x * b := by
    calc
      q * (x / q) * b + (x % q) * b = (q * (x / q) + x % q) * b := (Nat.add_mul _ _ b).symm
      _ = x * b := by rw [h_eq]
  have h_le : q * (x / q) * b ≤ x * b := by omega
  have h_sub : x * b - q * (x / q) * b = (x % q) * b := by omega
  rw [← h_sub]
  apply dvd_sub_of_dvd h_le hxb
  have h_assoc : q * (x / q) * b = (q * b) * (x / q) := by
    rw [Nat.mul_assoc, Nat.mul_comm (x / q) b, ← Nat.mul_assoc]
  rw [h_assoc]
  exact Nat.dvd_mul_right (q * b) (x / q)

/-- 2. Lemme d'Euclide en Lean 4 pur (descente complète dans Nat, sans Int ni Bézout) -/
theorem euclid_lemma {p a b : Nat} (hp : IsPrime p) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
    have hr0_lt : a % p < p := Nat.mod_lt a hp_pos
    have hr0_pos : 0 < a % p := by
      rcases Nat.eq_zero_or_pos (a % p) with hz | hpos
      · exact absurd (Nat.dvd_of_mod_eq_zero hz) hpa
      · exact hpos
    have hr0_dvd : p ∣ (a % p) * b :=
      dvd_mod_mul_of_dvd hp_pos hab (Nat.dvd_mul_right p b)
    suffices h_desc : ∀ m : Nat, 0 < m → m < p → p ∣ m * b → p ∣ b from
      h_desc (a % p) hr0_pos hr0_lt hr0_dvd
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm_pos hm_lt hmb
      by_cases hm_dvd_p : m ∣ p
      · rcases hp.2 m hm_dvd_p with hm1 | hmp
        · rw [hm1, Nat.one_mul] at hmb
          exact hmb
        · exfalso
          exact Nat.ne_of_lt hm_lt hmp
      · have hr_lt : p % m < m := Nat.mod_lt p hm_pos
        have hr_pos : 0 < p % m := by
          rcases Nat.eq_zero_or_pos (p % m) with hz | hpos
          · exact absurd (Nat.dvd_of_mod_eq_zero hz) hm_dvd_p
          · exact hpos
        have hr_dvd : p ∣ (p % m) * b :=
          dvd_mod_mul_of_dvd hm_pos (Nat.dvd_mul_right p b) hmb
        exact ih (p % m) hr_lt hr_pos (Nat.lt_trans hr_lt hm_lt) hr_dvd

/-- 3. Annulation modulaire modulo p premier -/
theorem mod_cancel_left {p a x y : Nat} (hp : IsPrime p) (hpa : ¬ (p ∣ a))
    (hmod : (a * x) % p = (a * y) % p) : x % p = y % p := by
  suffices h_le : ∀ u v : Nat, u ≤ v → (a * u) % p = (a * v) % p → u % p = v % p by
    rcases Nat.le_total x y with hxy | hyx
    · exact h_le x y hxy hmod
    · exact (h_le y x hyx hmod.symm).symm
  intro u v huv heq
  have hau_le_hav : a * u ≤ a * v := Nat.mul_le_mul_left a huv
  have hp_dvd_diff : p ∣ a * (v - u) := by
    rw [Nat.mul_sub_left_distrib]
    apply Nat.dvd_of_mod_eq_zero
    have h1 : a * v = p * (a * v / p) + (a * v) % p := (Nat.div_add_mod (a * v) p).symm
    have h2 : a * u = p * (a * u / p) + (a * u) % p := (Nat.div_add_mod (a * u) p).symm
    omega
  rcases euclid_lemma hp hp_dvd_diff with h_a | h_vu
  · exact absurd h_a hpa
  · rcases h_vu with ⟨k, hk⟩
    have hv : v = u + p * k := by omega
    rw [hv, Nat.add_mul_mod_self_left]

/-- 4. Lemme des racines carrées de 1 de Miller-Rabin -/
theorem miller_rabin_sqrt_one {p x : Nat} (hp : IsPrime p) (hx_pos : 1 ≤ x) (hx_lt : x < p)
    (hdvd : p ∣ (x - 1) * (x + 1)) : x = 1 ∨ x = p - 1 := by
  rcases euclid_lemma hp hdvd with h_minus | h_plus
  · left
    rcases h_minus with ⟨k, hk⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk_pos
    · omega
    · have : p ≤ p * k := Nat.le_mul_of_pos_right p hk_pos
      omega
  · right
    rcases h_plus with ⟨k, hk⟩
    have hk_ne0 : k ≠ 0 := by intro h0; subst h0; omega
    have hk_lt2 : k < 2 := by
      by_contra hge2
      have : p * 2 ≤ p * k := Nat.mul_le_mul_left p (by omega)
      omega
    have hk1 : k = 1 := by omega
    omega

/-- 5. Exponentiation modulaire binaire rapide O(log e) -/
def modPow (a e m : Nat) : Nat :=
  if m == 1 then 0
  else
    match e with
    | 0 => 1 % m
    | e + 1 =>
      let half := modPow ((a * a) % m) ((e + 1) / 2) m
      if (e + 1) % 2 == 0 then
        half
      else
        (a * half) % m
termination_by e
decreasing_by
  exact Nat.div_lt_self (Nat.zero_lt_succ _) (by decide)

theorem mod_pow_two_mul (a k m : Nat) : (((a * a) % m) ^ k) % m = (a ^ (2 * k)) % m := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod, ih, Nat.mod_mul_mod, ← Nat.mul_mod]
    have h_exp : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h_exp, Nat.pow_add, Nat.pow_two]
    have h_assoc : a ^ (2 * k) * (a * a) = a ^ (2 * k) * a * a := (Nat.mul_assoc _ _ _).symm
    rw [h_assoc]

/-- 6. Théorème de correction : modPow calcule exactement (a^e) % m -/
theorem modPow_correct (a e m : Nat) (hm : 1 < m) : modPow a e m = (a ^ e) % m := by
  induction e using Nat.strongRecOn generalizing a with
  | ind e ih =>
    unfold modPow
    have hm_ne1 : (m == 1) = false := by simp [Nat.ne_of_gt hm]
    rw [hm_ne1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases e with
    | zero => simp
    | succ e =>
      have h_lt : (e + 1) / 2 < e + 1 := Nat.div_lt_self (Nat.zero_lt_succ e) (by decide)
      have h_ih := ih ((e + 1) / 2) h_lt ((a * a) % m)
      dsimp only
      rw [h_ih]
      by_cases heven : ((e + 1) % 2 == 0) = true
      · rw [heven]
        simp only [↓reduceIte]
        rw [mod_pow_two_mul]
        exact congrArg (fun k => a ^ k % m) (by omega)
      · have heven_f : ((e + 1) % 2 == 0) = false := Bool.eq_false_iff.mpr heven
        rw [heven_f]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Nat.mul_mod, mod_pow_two_mul, Nat.mul_mod_mod, ← Nat.mul_mod]
        have h_div : 2 * ((e + 1) / 2) + 1 = e + 1 := by
          have h_rem : (e + 1) % 2 = 1 := by
            have hlt2 : (e + 1) % 2 < 2 := Nat.mod_lt (e + 1) (by decide)
            have hne0 : (e + 1) % 2 ≠ 0 := by
              intro hz
              apply heven
              simp [hz]
            omega
          have h_dm := Nat.div_add_mod (e + 1) 2
          omega
        have h_pow : a * a ^ (2 * ((e + 1) / 2)) = a ^ (e + 1) := by
          rw [← Nat.pow_succ']
          exact congrArg (fun k => a ^ k) h_div
        rw [h_pow]

/-- 7. Critère exécutable de témoin de Proth : a^((p-1)/2) ≡ p - 1 [MOD p] -/
def isProthWitness (a p : Nat) : Bool :=
  2 < p && p % 2 == 1 && modPow a ((p - 1) / 2) p == p - 1

#print axioms exists_prime_factor
#print axioms euclid_lemma
#print axioms mod_cancel_left
#print axioms miller_rabin_sqrt_one
#print axioms modPow_correct

end PurePrimality
