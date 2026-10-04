import Mathlib.Tactic

set_option linter.unusedSimpArgs false

/-! Necessary direction constraints for four centers, normalized so the
forbidden near-straight angular gap is 1 and pi is represented by t.
These definitions are not a replacement for the original Euclidean problem.
The geometry-to-directions bridge remains a separate obligation. -/
namespace JSP404.FourCenter

def TripleCap (a b c t : ℝ) : Prop :=
  (a < b ∧ b < c ∧ 1 ≤ c-a ∧ b-a ≤ t-1 ∧ c-b ≤ t-1) ∨
  (c < b ∧ b < a ∧ 1 ≤ a-c ∧ a-b ≤ t-1 ∧ b-c ≤ t-1)

def sortedGaps (a b c t : ℝ) : ℝ × ℝ × ℝ :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  let mid := a+b+c-lo-hi
  (mid-lo, hi-mid, t+lo-hi)

def High (n : ℝ) (g : ℝ × ℝ × ℝ) : Prop :=
  n ≤ g.1 ∨ n ≤ g.2.1 ∨ n ≤ g.2.2

def Middle (n : ℝ) (g : ℝ × ℝ × ℝ) : Prop :=
  n-1 ≤ g.1 ∨ n-1 ≤ g.2.1 ∨ n-1 ≤ g.2.2 ∨
  (2 ≤ g.1 ∧ 2 ≤ g.2.1 ∧ n ≤ g.1+g.2.1) ∨
  (2 ≤ g.1 ∧ 2 ≤ g.2.2 ∧ n ≤ g.1+g.2.2) ∨
  (2 ≤ g.2.1 ∧ 2 ≤ g.2.2 ∧ n ≤ g.2.1+g.2.2)

theorem sortedGaps_order_012 (a b c t : ℝ)
    (h0 : a ≤ b) (h1 : b ≤ c) :
    sortedGaps a b c t = (b-a,c-b,t+a-c) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

theorem sortedGaps_order_021 (a b c t : ℝ)
    (h0 : a ≤ c) (h1 : c ≤ b) :
    sortedGaps a b c t = (c-a,b-c,t+a-b) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

theorem sortedGaps_order_102 (a b c t : ℝ)
    (h0 : b ≤ a) (h1 : a ≤ c) :
    sortedGaps a b c t = (a-b,c-a,t+b-c) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

theorem sortedGaps_order_120 (a b c t : ℝ)
    (h0 : b ≤ c) (h1 : c ≤ a) :
    sortedGaps a b c t = (c-b,a-c,t+b-a) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

theorem sortedGaps_order_201 (a b c t : ℝ)
    (h0 : c ≤ a) (h1 : a ≤ b) :
    sortedGaps a b c t = (a-c,b-a,t+c-b) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

theorem sortedGaps_order_210 (a b c t : ℝ)
    (h0 : c ≤ b) (h1 : b ≤ a) :
    sortedGaps a b c t = (b-c,a-b,t+c-a) := by
  have h2 := le_trans h0 h1
  simp only [sortedGaps, min_eq_left h0, min_eq_right h0,
    min_eq_left h1, min_eq_right h1, min_eq_left h2, min_eq_right h2,
    max_eq_left h0, max_eq_right h0, max_eq_left h1, max_eq_right h1,
    max_eq_left h2, max_eq_right h2]
  ext <;> ring

end JSP404.FourCenter
