import Mathlib.Tactic

namespace JSP404.FourCenter

theorem four_sum_le_one_profile (k : Fin 4 → ℕ) (i : Fin 4) (a b : ℕ)
    (hi : k i ≤ a) (hrest : ∀ j, j ≠ i → k j ≤ b) :
    ∑ j, 2 ^ k j ≤ 2^a + 3*2^b := by
  have hpoint : ∀ j, 2^k j ≤ if j=i then 2^a else 2^b := by
    intro j
    split_ifs with h
    · subst j
      exact Nat.pow_le_pow_right (by decide) hi
    · exact Nat.pow_le_pow_right (by decide) (hrest j h)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hpoint j)
  have heq : (∑ j : Fin 4, if j=i then 2^a else 2^b) = 2^a+3*2^b := by
    fin_cases i <;> simp [Fin.sum_univ_succ] <;> omega
  simpa only [heq] using hs

theorem four_sum_le_two_profile (k : Fin 4 → ℕ) (i j : Fin 4) (a b c : ℕ)
    (hij : i ≠ j) (hi : k i ≤ a) (hj : k j ≤ b)
    (hrest : ∀ l, l ≠ i → l ≠ j → k l ≤ c) :
    ∑ l, 2 ^ k l ≤ 2^a+2^b+2*2^c := by
  have hpoint : ∀ l, 2^k l ≤ if l=i then 2^a else if l=j then 2^b else 2^c := by
    intro l
    split_ifs with h h'
    · subst l
      exact Nat.pow_le_pow_right (by decide) hi
    · subst l
      exact Nat.pow_le_pow_right (by decide) hj
    · exact Nat.pow_le_pow_right (by decide) (hrest l h h')
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun l _ ↦ hpoint l)
  have heq : (∑ l : Fin 4, if l=i then 2^a else if l=j then 2^b else 2^c) =
      2^a+2^b+2*2^c := by
    fin_cases i <;> fin_cases j <;> simp_all [Fin.sum_univ_succ] <;> omega
  simpa only [heq] using hs

private theorem powers_three_levels {n : ℕ} (hn : 3 ≤ n) :
    2^(n-2) = 2*2^(n-3) ∧ 2^(n-1) = 4*2^(n-3) ∧ 2^n = 8*2^(n-3) := by
  constructor
  · calc
      2^(n-2) = 2^((n-3)+1) := congrArg (fun r : ℕ ↦ 2^r) (by omega)
      _ = _ := by simp [pow_add]; omega
  constructor
  · calc
      2^(n-1) = 2^((n-3)+2) := congrArg (fun r : ℕ ↦ 2^r) (by omega)
      _ = _ := by norm_num [pow_add]; omega
  · calc
      2^n = 2^((n-3)+3) := congrArg (fun r : ℕ ↦ 2^r) (by omega)
      _ = _ := by norm_num [pow_add]; omega

/-- Four binary weights fit the lower half-period capacity if the two
forbidden near-maximum patterns are excluded. -/
theorem four_weight_lower (n : ℕ) (hn : 3 ≤ n) (k : Fin 4 → ℕ)
    (hmax : ∀ i, k i ≤ n-1)
    (hNoTwo : ∀ i j, i ≠ j → k i = n-1 → k j = n-1 → False)
    (hNoThree : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      k i = n-1 → n-2 ≤ k j → n-2 ≤ k l → False) :
    ∑ i, 2^k i ≤ 2^n := by
  obtain ⟨h2,h1,h0⟩ := powers_three_levels hn
  by_cases hex : ∃ i, k i = n-1
  · obtain ⟨i,hi⟩ := hex
    have hmid : ∀ j, j ≠ i → k j ≤ n-2 := by
      intro j hji
      have hm := hmax j
      have hne : k j ≠ n-1 := fun hj ↦ hNoTwo i j hji.symm hi hj
      omega
    obtain ⟨j,hji,hrest⟩ : ∃ j : Fin 4, j ≠ i ∧
        ∀ l, l ≠ i → l ≠ j → k l ≤ n-3 := by
      by_cases hm : ∃ j, j ≠ i ∧ n-2 ≤ k j
      · obtain ⟨j,hji,hj⟩ := hm
        refine ⟨j,hji,?_⟩
        intro l hli hlj
        have hnot : ¬ n-2 ≤ k l :=
          fun hl ↦ hNoThree i j l hji.symm hli.symm hlj.symm hi hj hl
        omega
      · obtain ⟨j,hji⟩ := exists_ne i
        refine ⟨j,hji,?_⟩
        intro l hli _
        have hnot : ¬ n-2 ≤ k l := fun hl ↦ hm ⟨l,hli,hl⟩
        omega
    have hb := four_sum_le_two_profile k i j (n-1) (n-2) (n-3)
      hji.symm (hmax i) (hmid j hji) hrest
    omega
  · have hmid : ∀ i, k i ≤ n-2 := by
      intro i
      have hm := hmax i
      have hne : k i ≠ n-1 := fun hi ↦ hex ⟨i,hi⟩
      omega
    have hb := four_sum_le_one_profile k 0 (n-2) (n-2) (hmid 0)
      (fun j _ ↦ hmid j)
    omega

/-- Four binary weights fit the upper half-period capacity if no two
maximum exponents coexist with a third near-maximum exponent. -/
theorem four_weight_upper (n : ℕ) (hn : 3 ≤ n) (k : Fin 4 → ℕ)
    (hmax : ∀ i, k i ≤ n-1)
    (hNoThree : ∀ i j l, i ≠ j → i ≠ l → j ≠ l →
      k i = n-1 → k j = n-1 → n-2 ≤ k l → False) :
    ∑ i, 2^k i ≤ 2^n+2^(n-2) := by
  obtain ⟨h2,h1,h0⟩ := powers_three_levels hn
  by_cases htwo : ∃ i j, i ≠ j ∧ k i = n-1 ∧ k j = n-1
  · obtain ⟨i,j,hij,hi,hj⟩ := htwo
    have hrest : ∀ l, l ≠ i → l ≠ j → k l ≤ n-3 := by
      intro l hli hlj
      have hnot : ¬ n-2 ≤ k l :=
        fun hl ↦ hNoThree i j l hij hli.symm hlj.symm hi hj hl
      omega
    have hb := four_sum_le_two_profile k i j (n-1) (n-1) (n-3)
      hij (hmax i) (hmax j) hrest
    omega
  · by_cases hex : ∃ i, k i = n-1
    · obtain ⟨i,hi⟩ := hex
      have hrest : ∀ j, j ≠ i → k j ≤ n-2 := by
        intro j hji
        have hm := hmax j
        have hne : k j ≠ n-1 := fun hj ↦ htwo ⟨i,j,hji.symm,hi,hj⟩
        omega
      have hb := four_sum_le_one_profile k i (n-1) (n-2) (hmax i) hrest
      omega
    · have hmid : ∀ j, k j ≤ n-2 := by
        intro j
        have hm := hmax j
        have hne : k j ≠ n-1 := fun hj ↦ hex ⟨j,hj⟩
        omega
      have hb := four_sum_le_one_profile k 0 (n-1) (n-2) (hmax 0)
        (fun j _ ↦ hmid j)
      omega

#print axioms four_weight_lower
#print axioms four_weight_upper
end JSP404.FourCenter
