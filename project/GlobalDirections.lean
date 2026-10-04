import FourCenterDefs

/-!
An arbitrary-cardinality direction model and a classical binary-band bound.
The binary-color argument is classical Erdős–Szekeres; related formalizations
were inspected in prior PR 300. This is not a new mathematical discovery.

This file supplies the bound s <= 2^k when the normalized period t <= k.
Taking k = ceil(t) is generally too weak for the sharp Sendov intervals.
The original Euclidean-to-model bridge and sharp bounds remain unproved.
-/
namespace JSP404.GlobalDirections

structure Model (s : ℕ) (t : ℝ) where
  direction : Fin s → Fin s → ℝ
  range : ∀ i j, i < j → 0 ≤ direction i j ∧ direction i j < t
  triangle : ∀ i j k, i < j → j < k →
    FourCenter.TripleCap (direction i j) (direction i k) (direction j k) t

theorem Model.middle_separation {s : ℕ} {t : ℝ} (M : Model s t)
    (i j k : Fin s) (hij : i < j) (hjk : j < k) :
    1 ≤ |M.direction i j - M.direction j k| := by
  rcases M.triangle i j k hij hjk with h | h
  · rw [abs_of_neg (by linarith [h.1, h.2.1])]
    linarith [h.2.2.1]
  · rw [abs_of_pos (by linarith [h.1, h.2.1])]
    exact h.2.2.1

/-- Assign a bit according to whether a vertex has an incoming edge in a band.
For an edge in that band, its endpoints have different bits. -/
theorem cardinality_bound {s : ℕ} {t : ℝ} (M : Model s t)
    (k : ℕ) (ht : t ≤ k) : s ≤ 2 ^ k := by
  classical
  let incoming : Fin s → Fin k → Prop := fun j b ↦
    ∃ i, i < j ∧ (b : ℝ) ≤ M.direction i j ∧ M.direction i j < (b : ℝ) + 1
  let code : Fin s → (Fin k → Bool) := fun j b ↦ decide (incoming j b)
  have different : ∀ i j : Fin s, i < j → code i ≠ code j := by
    intro i j hij heq
    have hr := M.range i j hij
    have hfloor : Nat.floor (M.direction i j) < k :=
      (Nat.floor_lt hr.1).2 (hr.2.trans_le ht)
    let b : Fin k := ⟨Nat.floor (M.direction i j), hfloor⟩
    have hlo : (b : ℝ) ≤ M.direction i j := by
      exact Nat.floor_le hr.1
    have hhi : M.direction i j < (b : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hin : incoming j b := ⟨i, hij, hlo, hhi⟩
    have hout : ¬ incoming i b := by
      rintro ⟨a, hai, halo, hahi⟩
      have hsep := M.middle_separation a i j hai hij
      have hclose : |M.direction a i - M.direction i j| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      exact (not_lt_of_ge hsep) hclose
    have hbit := congrFun heq b
    simp only [code, decide_eq_false hout, decide_eq_true hin] at hbit
    cases hbit
  have injective : Function.Injective code := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact different i j hlt hij
    · exact different j i hgt hij.symm
  simpa using Fintype.card_le_of_injective code injective

#print axioms Model.middle_separation
#print axioms cardinality_bound
end JSP404.GlobalDirections
