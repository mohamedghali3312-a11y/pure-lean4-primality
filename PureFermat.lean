import PurePrimality

namespace PureFermat
open PurePrimality

/-- Factorielle naturelle n! -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Produit des éléments d'une liste -/
def prodList : List Nat → Nat
  | [] => 1
  | x :: xs => x * prodList xs

/-- Liste [1, 2, ..., n] -/
def range1 : Nat → List Nat
  | 0 => []
  | n + 1 => range1 n ++ [n + 1]

theorem prodList_append (l1 l2 : List Nat) :
    prodList (l1 ++ l2) = prodList l1 * prodList l2 := by
  induction l1 with
  | nil => simp [prodList]
  | cons x xs ih => simp [prodList, ih, Nat.mul_assoc]

theorem prodList_range1 : ∀ n : Nat, prodList (range1 n) = fact n
  | 0 => rfl
  | n + 1 => by
    unfold range1 fact
    rw [prodList_append, prodList_range1 n]
    simp [prodList, Nat.mul_comm]

theorem length_range1 : ∀ n : Nat, (range1 n).length = n
  | 0 => rfl
  | n + 1 => by simp [range1, length_range1 n]

/-- 1. Invariance du produit sous toute permutation de liste -/
theorem prodList_perm {l1 l2 : List Nat} (h : l1.Perm l2) :
    prodList l1 = prodList l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [prodList, ih]
  | swap x y l =>
    simp only [prodList]
    ac_rfl
  | trans _ _ ih1 ih2 => exact Eq.trans ih1 ih2

/-- 2. Principe des tiroirs : une liste sans doublon dans [1..n] a longueur ≤ n -/
theorem nodup_length_le : ∀ (n : Nat) (l : List Nat),
    l.Nodup → (∀ x ∈ l, 1 ≤ x ∧ x ≤ n) → l.length ≤ n
  | 0, l, _, hmem => by
    cases l with
    | nil => exact Nat.le_refl 0
    | cons x _ =>
      have := (hmem x (by simp)).1
      have := (hmem x (by simp)).2
      omega
  | n + 1, l, hnodup, hmem => by
    by_cases hin : (n + 1) ∈ l
    · have hperm : l.Perm ((n + 1) :: l.erase (n + 1)) := List.perm_cons_erase hin
      have hlen : l.length = (l.erase (n + 1)).length + 1 := by
        rw [hperm.length_eq]; simp
      have hnodup' : (l.erase (n + 1)).Nodup := (hnodup.perm hperm).of_cons
      have hmem' : ∀ x ∈ l.erase (n + 1), 1 ≤ x ∧ x ≤ n := by
        intro x hx
        have hx_in : x ∈ l := List.mem_of_mem_erase hx
        have hx_ne : x ≠ n + 1 := fun h => (List.nodup_cons.mp (hnodup.perm hperm)).1 (h ▸ hx)
        have hb := hmem x hx_in
        omega
      have ih := nodup_length_le n (l.erase (n + 1)) hnodup' hmem'
      omega
    · have hmem' : ∀ x ∈ l, 1 ≤ x ∧ x ≤ n := by
        intro x hx
        have hb := hmem x hx
        have hne : x ≠ n + 1 := fun h => hin (h ▸ hx)
        omega
      exact Nat.le_trans (nodup_length_le n l hnodup hmem') (Nat.le_succ n)

/-- 3. Toute liste sans doublon de longueur n dans [1..n] est une permutation de range1 n -/
theorem nodup_range1_perm : ∀ (n : Nat) (l : List Nat),
    l.Nodup → l.length = n → (∀ x ∈ l, 1 ≤ x ∧ x ≤ n) → l.Perm (range1 n)
  | 0, l, _, hlen, _ => by
    cases l with
    | nil => exact List.Perm.refl []
    | cons _ _ => simp at hlen
  | n + 1, l, hnodup, hlen, hmem => by
    have hin : (n + 1) ∈ l := by
      by_contra hnot
      have hmem' : ∀ x ∈ l, 1 ≤ x ∧ x ≤ n := by
        intro x hx
        have hb := hmem x hx
        have hne : x ≠ n + 1 := fun h => hnot (h ▸ hx)
        omega
      have hle := nodup_length_le n l hnodup hmem'
      omega
    have hperm_head : l.Perm ((n + 1) :: l.erase (n + 1)) := List.perm_cons_erase hin
    have hlen' : (l.erase (n + 1)).length = n := by
      have := hperm_head.length_eq
      simp at this
      omega
    have hnodup' : (l.erase (n + 1)).Nodup := (hnodup.perm hperm_head).of_cons
    have hmem' : ∀ x ∈ l.erase (n + 1), 1 ≤ x ∧ x ≤ n := by
      intro x hx
      have hx_in : x ∈ l := List.mem_of_mem_erase hx
      have hx_ne : x ≠ n + 1 := fun h => (List.nodup_cons.mp (hnodup.perm hperm_head)).1 (h ▸ hx)
      have hb := hmem x hx_in
      omega
    have ih := nodup_range1_perm n (l.erase (n + 1)) hnodup' hlen' hmem'
    have hstep : ((n + 1) :: l.erase (n + 1)).Perm ((n + 1) :: range1 n) := ih.cons (n + 1)
    have hrot : ((n + 1) :: range1 n).Perm (range1 n ++ [n + 1]) :=
      List.perm_append_comm
    exact hperm_head.trans (hstep.trans hrot)

/-- Lemme autonome : une fonction injective sur une liste sans doublon préserve Nodup -/
theorem nodup_map_inj {f : Nat → Nat} : ∀ (l : List Nat),
    l.Nodup → (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: xs, hnodup, hinj => by
    rw [List.nodup_cons] at hnodup ⊢
    rcases hnodup with ⟨hx_not_in, hxs_nodup⟩
    refine ⟨?_, nodup_map_inj xs hxs_nodup (fun u hu v hv heq =>
      hinj u (List.mem_cons_of_mem x hu) v (List.mem_cons_of_mem x hv) heq)⟩
    intro hmem_map
    rw [List.mem_map] at hmem_map
    rcases hmem_map with ⟨y, hy_in, hfy⟩
    have hxy : x = y := hinj x (List.mem_cons_self ..) y (List.mem_cons_of_mem x hy_in) hfy.symm
    exact hx_not_in (hxy ▸ hy_in)

theorem prime_not_dvd_lt {p k : Nat} (hk_pos : 1 ≤ k) (hk_lt : k < p) :
    ¬ (p ∣ k) := by
  intro hdvd
  have hle : p ≤ k := Nat.le_of_dvd (by omega) hdvd
  omega

theorem prime_not_dvd_fact_pred {p : Nat} (hp : IsPrime p) :
    ¬ (p ∣ fact (p - 1)) := by
  suffices h : ∀ k : Nat, k < p → ¬ (p ∣ fact k) from
    h (p - 1) (by have := hp.1; omega)
  intro k
  induction k with
  | zero =>
    intro _ hdvd
    have hle : p ≤ 1 := Nat.le_of_dvd (by decide) hdvd
    have := hp.1
    omega
  | succ k ih =>
    intro hlt hdvd
    unfold fact at hdvd
    rcases euclid_lemma hp hdvd with h_head | h_tail
    · exact prime_not_dvd_lt (by omega) hlt h_head
    · exact ih (by omega) h_tail

theorem range1_mem_bounds : ∀ (n x : Nat), x ∈ range1 n → 1 ≤ x ∧ x ≤ n
  | 0, x, hx => by simp [range1] at hx
  | n + 1, x, hx => by
    simp only [range1, List.mem_append, List.mem_singleton] at hx
    rcases hx with h_left | rfl
    · have hb := range1_mem_bounds n x h_left
      omega
    · omega

theorem range1_nodup : ∀ n : Nat, (range1 n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    unfold range1
    rw [List.nodup_append]
    refine ⟨range1_nodup n, by simp, ?_⟩
    intro x hx y hy
    simp at hy
    subst hy
    have hb := range1_mem_bounds n x hx
    omega

theorem prodList_map_mul (a : Nat) : ∀ l : List Nat,
    prodList (l.map (fun k => a * k)) = a ^ l.length * prodList l
  | [] => by simp [prodList]
  | x :: xs => by
    simp only [List.map_cons, prodList, List.length_cons]
    rw [prodList_map_mul a xs]
    calc
      (a * x) * (a ^ xs.length * prodList xs)
        = (a * a ^ xs.length) * (x * prodList xs) := by ac_rfl
      _ = a ^ (xs.length + 1) * (x * prodList xs) := by rw [← Nat.pow_succ']

/-- 4. PETIT THÉORÈME DE FERMAT COMPLET (100 % AUTONOME, 0 MATHLIB, 0 SORRYAX) :
    Pour tout nombre premier p et tout entier a non divisible par p, a^(p - 1) % p = 1 -/
theorem fermat_little_theorem {p a : Nat} (hp : IsPrime p) (hpa : ¬ (p ∣ a)) :
    a ^ (p - 1) % p = 1 := by
  let resList := (range1 (p - 1)).map (fun k => (a * k) % p)
  have hp_pos : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hbounds : ∀ y ∈ resList, 1 ≤ y ∧ y ≤ p - 1 := by
    intro y hy
    simp only [resList, List.mem_map] at hy
    rcases hy with ⟨k, hk, rfl⟩
    have hkb := range1_mem_bounds (p - 1) k hk
    have hlt : (a * k) % p < p := Nat.mod_lt (a * k) hp_pos
    have hne0 : (a * k) % p ≠ 0 := by
      intro hz
      have hdvd : p ∣ a * k := Nat.dvd_of_mod_eq_zero hz
      rcases euclid_lemma hp hdvd with h_a | h_k
      · exact hpa h_a
      · exact prime_not_dvd_lt hkb.1 (by omega) h_k
    omega
  have hnodup_res : resList.Nodup := by
    apply nodup_map_inj (range1 (p - 1)) (range1_nodup (p - 1))
    intro x hx y hy heq
    have hxb := range1_mem_bounds (p - 1) x hx
    have hyb := range1_mem_bounds (p - 1) y hy
    have hmod_xy : x % p = y % p := mod_cancel_left hp hpa heq
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod_xy
    exact hmod_xy
  have hlen_res : resList.length = p - 1 := by
    simp [resList, length_range1]
  have hperm : resList.Perm (range1 (p - 1)) :=
    nodup_range1_perm (p - 1) resList hnodup_res hlen_res hbounds
  have hprod_eq : prodList resList % p = prodList (range1 (p - 1)) % p :=
    congrArg (fun z => z % p) (prodList_perm hperm)
  have hmod_map : prodList resList % p = prodList ((range1 (p - 1)).map (fun k => a * k)) % p := by
    dsimp [resList]
    induction (range1 (p - 1)) with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.map_cons, prodList]
      rw [Nat.mul_mod, Nat.mod_mod, ih, ← Nat.mul_mod]
  rw [hmod_map, prodList_map_mul, length_range1, prodList_range1] at hprod_eq
  have hcomm : (fact (p - 1) * a ^ (p - 1)) % p = (fact (p - 1) * 1) % p := by
    simpa [Nat.mul_comm, Nat.one_mul] using hprod_eq
  have hres := mod_cancel_left hp (prime_not_dvd_fact_pred hp) hcomm
  have hp_gt1 : 1 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  rw [Nat.mod_eq_of_lt hp_gt1] at hres
  exact hres

#print axioms fermat_little_theorem

end PureFermat
