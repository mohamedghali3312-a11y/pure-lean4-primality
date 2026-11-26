/-- 2. Lemme d'Euclide en Lean 4 pur (descente complète sur m ≤ p, 0 sorryAx) -/
theorem euclid_lemma {p a b : Nat} (hp : IsPrime p) (hab : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  by_cases hpa : p ∣ a
  · exact Or.inl hpa
  · right
    -- On ramène d'abord a à r0 = a % p, qui vérifie 0 < r0 < p et p ∣ r0 * b
    have hp_pos : 0 < p := by have := hp.1; omega
    have hr0_lt : a % p < p := Nat.mod_lt a hp_pos
    have hr0_pos : 0 < a % p := by
      rcases Nat.eq_zero_or_pos (a % p) with hz | hpos
      · exact absurd (Nat.dvd_of_mod_eq_zero hz) hpa
      · exact hpos
    have hr0_dvd : p ∣ (a % p) * b :=
      dvd_mod_mul_of_dvd hp_pos hab (Nat.dvd_mul_right p b)
    -- Désormais tout m tel que 0 < m < p et p ∣ m * b descend strictement jusqu'à 1 !
    suffices h_desc : ∀ m : Nat, 0 < m → m < p → p ∣ m * b → p ∣ b from
      h_desc (a % p) hr0_pos hr0_lt hr0_dvd
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm_pos hm_lt hmb
      by_cases hm_dvd_p : m ∣ p
      · rcases hp.2 m hm_dvd_p with rfl | rfl
        · simpa using hmb
        · omega
      · have hr_lt : p % m < m := Nat.mod_lt p hm_pos
        have hr_pos : 0 < p % m := by
          rcases Nat.eq_zero_or_pos (p % m) with hz | hpos
          · exact absurd (Nat.dvd_of_mod_eq_zero hz) hm_dvd_p
          · exact hpos
        have hr_dvd : p ∣ (p % m) * b :=
          dvd_mod_mul_of_dvd hm_pos (Nat.dvd_mul_right p b) hmb
        exact ih (p % m) hr_lt hr_pos (by omega) hr_dvd
