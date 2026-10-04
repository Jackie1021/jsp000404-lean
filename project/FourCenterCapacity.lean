import FourCenterExclusions

namespace JSP404.FourCenter

structure DirectionModel (t : ℝ) where
  d01 : ℝ
  d02 : ℝ
  d03 : ℝ
  d12 : ℝ
  d13 : ℝ
  d23 : ℝ
  r01 : 0 ≤ d01 ∧ d01 < t
  r02 : 0 ≤ d02 ∧ d02 < t
  r03 : 0 ≤ d03 ∧ d03 < t
  r12 : 0 ≤ d12 ∧ d12 < t
  r13 : 0 ≤ d13 ∧ d13 < t
  r23 : 0 ≤ d23 ∧ d23 < t
  c012 : TripleCap d01 d02 d12 t
  c013 : TripleCap d01 d03 d13 t
  c023 : TripleCap d02 d03 d23 t
  c123 : TripleCap d12 d13 d23 t

def DirectionModel.gaps {t : ℝ} (M : DirectionModel t) : Fin 4 → ℝ × ℝ × ℝ :=
  ![sortedGaps M.d01 M.d02 M.d03 t,
    sortedGaps M.d01 M.d12 M.d13 t,
    sortedGaps M.d02 M.d12 M.d23 t,
    sortedGaps M.d03 M.d13 M.d23 t]

theorem sortedGaps_sum (a b c t : ℝ) :
    (sortedGaps a b c t).1 + (sortedGaps a b c t).2.1 +
      (sortedGaps a b c t).2.2 = t := by
  simp only [sortedGaps]
  ring

theorem DirectionModel.gaps_sum {t : ℝ} (M : DirectionModel t) (i : Fin 4) :
    (M.gaps i).1 + (M.gaps i).2.1 + (M.gaps i).2.2 = t := by
  fin_cases i <;> exact sortedGaps_sum _ _ _ _

/-- An explicit floor certificate for the three cyclic gaps. -/
structure CapacityData (g : ℝ × ℝ × ℝ) where
  a : ℕ
  b : ℕ
  c : ℕ
  a_lo : (a : ℝ) ≤ g.1
  b_lo : (b : ℝ) ≤ g.2.1
  c_lo : (c : ℝ) ≤ g.2.2
  a_hi : g.1 < (a : ℝ)+1
  b_hi : g.2.1 < (b : ℝ)+1
  c_hi : g.2.2 < (c : ℝ)+1

def CapacityData.exponent {g : ℝ × ℝ × ℝ} (C : CapacityData g) : ℕ :=
  (C.a-1)+(C.b-1)+(C.c-1)

theorem CapacityData.floor_budget {g : ℝ × ℝ × ℝ} {t : ℝ} {n : ℕ}
    (C : CapacityData g) (hsum : g.1+g.2.1+g.2.2=t) (ht : t < (n : ℝ)+1) :
    C.a+C.b+C.c ≤ n := by
  have h : ((C.a+C.b+C.c : ℕ) : ℝ) < ((n+1 : ℕ) : ℝ) := by
    push_cast
    linarith [C.a_lo,C.b_lo,C.c_lo]
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h)

theorem CapacityData.exponent_le {g : ℝ × ℝ × ℝ} {n : ℕ}
    (C : CapacityData g) (hn : 1 ≤ n) (hb : C.a+C.b+C.c ≤ n) :
    C.exponent ≤ n-1 := by
  simp only [CapacityData.exponent]
  omega

theorem CapacityData.high_of_exponent {g : ℝ × ℝ × ℝ} {n : ℕ}
    (C : CapacityData g) (hn : 3 ≤ n) (hb : C.a+C.b+C.c ≤ n)
    (hk : C.exponent = n-1) : High n g := by
  have hf : n ≤ C.a ∨ n ≤ C.b ∨ n ≤ C.c := by
    simp only [CapacityData.exponent] at hk
    omega
  rcases hf with ha | hb | hc
  · exact Or.inl ((by exact_mod_cast ha : (n : ℝ) ≤ C.a).trans C.a_lo)
  · exact Or.inr (Or.inl ((by exact_mod_cast hb : (n : ℝ) ≤ C.b).trans C.b_lo))
  · exact Or.inr (Or.inr ((by exact_mod_cast hc : (n : ℝ) ≤ C.c).trans C.c_lo))

theorem CapacityData.middle_of_exponent {g : ℝ × ℝ × ℝ} {n : ℕ}
    (C : CapacityData g) (hn : 3 ≤ n) (hb : C.a+C.b+C.c ≤ n)
    (hk : n-2 ≤ C.exponent) : Middle n g := by
  have hf : n-1 ≤ C.a ∨ n-1 ≤ C.b ∨ n-1 ≤ C.c ∨
      (2 ≤ C.a ∧ 2 ≤ C.b ∧ n ≤ C.a+C.b) ∨
      (2 ≤ C.a ∧ 2 ≤ C.c ∧ n ≤ C.a+C.c) ∨
      (2 ≤ C.b ∧ 2 ≤ C.c ∧ n ≤ C.b+C.c) := by
    simp only [CapacityData.exponent] at hk
    omega
  have hcast : ((n-1 : ℕ) : ℝ) = (n : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rcases hf with ha | hb | hc | ⟨ha,hb,hab⟩ | ⟨ha,hc,hac⟩ | ⟨hb,hc,hbc⟩
  · apply Or.inl
    have h : ((n-1 : ℕ) : ℝ) ≤ C.a := by exact_mod_cast ha
    linarith [C.a_lo]
  · apply Or.inr ∘ Or.inl
    have h : ((n-1 : ℕ) : ℝ) ≤ C.b := by exact_mod_cast hb
    linarith [C.b_lo]
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    have h : ((n-1 : ℕ) : ℝ) ≤ C.c := by exact_mod_cast hc
    linarith [C.c_lo]
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    have ha' : (2 : ℝ) ≤ C.a := by exact_mod_cast ha
    have hb' : (2 : ℝ) ≤ C.b := by exact_mod_cast hb
    have hab' : (n : ℝ) ≤ (C.a : ℝ)+C.b := by exact_mod_cast hab
    exact ⟨ha'.trans C.a_lo, hb'.trans C.b_lo, by linarith [C.a_lo,C.b_lo]⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    have ha' : (2 : ℝ) ≤ C.a := by exact_mod_cast ha
    have hc' : (2 : ℝ) ≤ C.c := by exact_mod_cast hc
    have hac' : (n : ℝ) ≤ (C.a : ℝ)+C.c := by exact_mod_cast hac
    exact ⟨ha'.trans C.a_lo, hc'.trans C.c_lo, by linarith [C.a_lo,C.c_lo]⟩
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    have hb' : (2 : ℝ) ≤ C.b := by exact_mod_cast hb
    have hc' : (2 : ℝ) ≤ C.c := by exact_mod_cast hc
    have hbc' : (n : ℝ) ≤ (C.b : ℝ)+C.c := by exact_mod_cast hbc
    exact ⟨hb'.trans C.b_lo, hc'.trans C.c_lo, by linarith [C.b_lo,C.c_lo]⟩

theorem no_two_high_lower {n t : ℝ} (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n+1/2) (M : DirectionModel t) (i j : Fin 4) (hij : i ≠ j)
    (hi : High n (M.gaps i)) (hj : High n (M.gaps j)) : False := by
  fin_cases i <;> fin_cases j
  · exact hij rfl
  · exact lower_no_two_high_01 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_02 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_03 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_01 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact hij rfl
  · exact lower_no_two_high_12 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_13 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_02 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact lower_no_two_high_12 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact hij rfl
  · exact lower_no_two_high_23 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj
  · exact lower_no_two_high_03 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact lower_no_two_high_13 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact lower_no_two_high_23 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi
  · exact hij rfl

theorem no_high_two_middle_lower {n t : ℝ} (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n+1/2) (M : DirectionModel t) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : High n (M.gaps i)) (hj : Middle n (M.gaps j))
    (hk : Middle n (M.gaps k)) : False := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hik rfl
  · exact hjk rfl
  · exact lower_no_high_middle_middle_012 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact lower_no_high_middle_middle_013 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact lower_no_high_middle_middle_012 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact lower_no_high_middle_middle_023 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact lower_no_high_middle_middle_013 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact lower_no_high_middle_middle_023 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact hjk rfl
  · exact hik rfl
  · exact lower_no_high_middle_middle_102 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact lower_no_high_middle_middle_103 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact lower_no_high_middle_middle_102 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hik rfl
  · exact hjk rfl
  · exact lower_no_high_middle_middle_123 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact lower_no_high_middle_middle_103 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hik rfl
  · exact lower_no_high_middle_middle_123 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact hjk rfl
  · exact lower_no_high_middle_middle_201 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact lower_no_high_middle_middle_203 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact lower_no_high_middle_middle_201 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact hik rfl
  · exact lower_no_high_middle_middle_213 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact lower_no_high_middle_middle_203 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact lower_no_high_middle_middle_213 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hik rfl
  · exact hjk rfl
  · exact hjk rfl
  · exact lower_no_high_middle_middle_301 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact lower_no_high_middle_middle_302 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact lower_no_high_middle_middle_301 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact lower_no_high_middle_middle_312 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact lower_no_high_middle_middle_302 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact lower_no_high_middle_middle_312 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hk hj
  · exact hjk rfl
  · exact hik rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl

theorem no_two_high_middle_upper {n t : ℝ} (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n+1) (hhalf : n+1/2 ≤ t) (M : DirectionModel t) (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : High n (M.gaps i)) (hj : High n (M.gaps j))
    (hk : Middle n (M.gaps k)) : False := by
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hik rfl
  · exact hjk rfl
  · exact upper_no_high_high_middle_012 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact upper_no_high_high_middle_013 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact upper_no_high_high_middle_021 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hjk rfl
  · exact upper_no_high_high_middle_023 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact upper_no_high_high_middle_031 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact upper_no_high_high_middle_032 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hjk rfl
  · exact hjk rfl
  · exact hik rfl
  · exact upper_no_high_high_middle_012 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact upper_no_high_high_middle_013 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact upper_no_high_high_middle_120 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact hjk rfl
  · exact upper_no_high_high_middle_123 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact upper_no_high_high_middle_130 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact upper_no_high_high_middle_132 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hjk rfl
  · exact hjk rfl
  · exact upper_no_high_high_middle_021 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hik rfl
  · exact upper_no_high_high_middle_023 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact upper_no_high_high_middle_120 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hjk rfl
  · exact hik rfl
  · exact upper_no_high_high_middle_123 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact upper_no_high_high_middle_230 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact upper_no_high_high_middle_231 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hi hj hk
  · exact hik rfl
  · exact hjk rfl
  · exact hjk rfl
  · exact upper_no_high_high_middle_031 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact upper_no_high_high_middle_032 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hik rfl
  · exact upper_no_high_high_middle_130 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hjk rfl
  · exact upper_no_high_high_middle_132 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hik rfl
  · exact upper_no_high_high_middle_230 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact upper_no_high_high_middle_231 n t M.d01 M.d02 M.d03 M.d12 M.d13 M.d23 hn ht htop hhalf M.r01 M.r02 M.r03 M.r12 M.r13 M.r23 M.c012 M.c013 M.c023 M.c123 hj hi hk
  · exact hjk rfl
  · exact hik rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl
  · exact hij rfl

end JSP404.FourCenter
