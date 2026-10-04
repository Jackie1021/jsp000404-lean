import FourCenterDefs

/-! Generated exhaustive case proofs for the four-center direction relaxation.
Z3 selected linear contradiction cores; every inference below is independently
constructed by Lean's linarith tactic and checked by the Lean kernel.
This is a restricted intermediate result, not the full original problem. -/
set_option maxHeartbeats 0
set_option linter.unusedVariables false
namespace JSP404.FourCenter

theorem lower_no_two_high_01 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d01lo, d23hi, h123_2, P0a, h012_1]
    · linarith only [P0a, h013_3, h012_0, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_2, htop, d01lo, d23hi, P1a]
      · linarith only [d13hi, h012_2, htop, P1a, d01lo]
      · linarith only [h012_2, P1a, h123_0, htop]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, htop, d01lo, d12hi, P0a, h123_2]
    · linarith only [h013_3, P0a, htop, h012_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_0, htop, h123_1, P1a, h012_4, P0a]
      · linarith only [P1a, h012_0, d01lo, d12hi, h123_0, htop, h023_2]
      · linarith only [h012_0, h123_2, htop, P1a, h023_2]
  · linarith only [h023_2, h123_1, h123_0, h012_1]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, htop, P0a]
    · linarith only [htop, h012_3, P0a, h013_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, P0a, h023_2, d23lo, htop, h123_1, d12hi]
      · linarith only [htop, d23lo, h013_2, d12hi, P0a, h023_2, P1a]
      · linarith only [h123_1, h013_2, P1a, htop]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_0, htop, h012_2, d23lo, d12hi, h123_0]
    · linarith only [h123_0, htop, d02hi, P0a, h013_2, d23lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_0, d12hi, h012_2, P1a, htop, d23lo]
      · linarith only [d23lo, d12hi, h123_0, h013_2, P1a, htop]
      · linarith only [P1a, htop, h012_2, h013_2]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, h013_2, htop, h012_0, P0a, d13hi]
    · linarith only [P0a, htop, h012_2, d12lo, d03hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, d13hi, P1a, d12lo, htop]
      · linarith only [h012_2, d12lo, d13hi, htop, P1a]
      · linarith only [htop, h013_2, P1a, h012_2]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h012_1, h023_1, h013_0]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_1, P0a, h012_3, htop]
    · linarith only [h012_3, htop, P0a, h023_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, h013_2, d12lo, P1a]
      · linarith only [h023_2, d23hi, d12lo, P1a, htop, P0a, h123_0]
      · linarith only [htop, h123_0, P1a, h013_2]
  · linarith only [h023_1, h123_0, h013_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, h023_0, d12lo, P0a, h012_1, htop, h123_2]
    · linarith only [h023_2, htop, d12lo, d01hi, P0a, h123_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_1, d01hi, h023_2, d12lo, htop, P1a, h012_1]
      · linarith only [P1a, h012_4, h123_0, htop, h023_1, P0a]
      · linarith only [P1a, htop, h023_2, h123_2, h012_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, P0a, h012_1, htop]
    · linarith only [h012_0, d01hi, d23lo, P0a, htop, h123_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h123_0, d23lo, h012_2, htop, d01hi]
      · linarith only [P1a, d23lo, htop, d01hi, h123_2]
      · linarith only [P1a, h013_2, htop]
#print axioms lower_no_two_high_01

theorem lower_no_two_high_02 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, d23hi, d01lo, htop, h123_2, P0a]
    · linarith only [h012_0, h013_3, htop, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_2, h012_0, P1a, d01lo, d23hi, htop]
      · linarith only [P1a, d01lo, d23hi, h012_2, htop]
      · linarith only [P1a, h012_1, htop, h123_2]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h123_2, d12hi, htop, d01lo, h023_2]
    · linarith only [P0a, h013_3, htop, h012_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h012_0, d12hi, h123_2, d01lo, P1a, htop]
      · linarith only [d12hi, htop, h023_2, P1a, d01lo, h012_0]
      · linarith only [h023_2, P1a, htop, h123_2]
  · linarith only [h023_2, h123_0, h012_1, h123_1]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h013_3]
    · linarith only [h013_0, h012_3, htop, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, d23lo, P0a, P1a, h123_1, htop, d12hi]
      · linarith only [d12hi, h023_2, d23lo, htop, P1a]
      · linarith only [htop, h013_2, h123_1, P1a, h023_2, P0a]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h013_2, h012_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h123_0, d12hi, h012_2, d23lo, h013_0, htop]
    · linarith only [htop, h123_0, d02hi, h013_2, d23lo, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_1, htop, P0a, h012_2, d23lo, d12hi, P1a]
      · linarith only [P1a, h012_0, h013_2, htop, d23lo, h123_0, d12hi]
      · linarith only [h012_2, h013_2, htop, h123_0, P1a]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, d12lo, P0a, h013_2, h012_0, htop]
    · linarith only [h012_2, d12lo, P0a, d03hi, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, h012_1, P1a, htop, h013_2, d13hi]
      · linarith only [htop, P1a, h012_2, P0a, d23hi, h013_0, d12lo]
      · linarith only [htop, P1a, h012_2, h013_2, h123_1]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h013_0, h012_1, h023_1]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_1, h012_3]
    · linarith only [h012_3, htop, h023_0, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d23hi, P1a, d12lo, h023_2, htop]
      · linarith only [h123_0, h013_2, d12lo, d23hi, P0a, P1a, htop]
      · linarith only [h123_0, P1a, htop, h013_2, h023_2, P0a]
  · linarith only [h123_0, h013_0, h023_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d12lo, h123_2, d01hi, h023_0, htop, h012_1]
    · linarith only [htop, P0a, h023_2, h123_2, d01hi, d12lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h012_1, d01hi, h023_2, d12lo]
      · linarith only [h123_2, d12lo, htop, d01hi, h012_1, P1a]
      · linarith only [h123_2, htop, h023_2, P1a]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_3, h012_1]
    · linarith only [h123_2, d01hi, d23lo, h012_0, htop, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h012_2, d01hi, d23lo]
      · linarith only [d23lo, P1a, h012_1, htop, d01hi, h123_2]
      · linarith only [h123_2, h012_0, htop, P1a]
#print axioms lower_no_two_high_02

theorem lower_no_two_high_03 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, P0a, htop, d01lo, h012_1, d23hi]
    · linarith only [h012_0, P0a, htop, h013_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h013_4, P1a]
      · linarith only [h123_0, htop, d23hi, P1a, d01lo, h012_2]
      · linarith only [h123_2, htop, P0a, P1a, h012_2]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12hi, h123_2, P0a, d01lo, htop, h023_2]
    · linarith only [P0a, h013_3, h012_0, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01lo, P1a, d12hi, h023_0, h123_2, h012_0, htop]
      · linarith only [h012_0, d01lo, P1a, d13hi, h023_2, htop]
      · linarith only [P1a, h123_0, h023_2, htop, h012_0, P0a]
  · linarith only [h012_1, h123_1, h123_0, h023_2]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, P0a, htop]
    · linarith only [P0a, h013_0, h012_3, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12hi, htop, d23lo, h023_1, h012_2, P1a, P0a]
      · linarith only [h123_1, d23lo, d12hi, h013_0, h023_2, htop, P0a, P1a]
      · linarith only [htop, h023_2, h013_2, P1a, P0a]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, h013_0, htop, P0a, d23lo, h123_0, d12hi]
    · linarith only [P0a, d23lo, h123_0, d02hi, htop, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, P1a, d23lo, h013_2]
      · linarith only [P1a, d23lo, d12hi, h123_0, h013_1, h012_2, htop]
      · linarith only [h012_0, h123_0, htop, P0a, h013_2, P1a]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h012_0, d13hi, h013_2, d12lo, P0a]
    · linarith only [d03hi, P0a, d12lo, h012_2, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_0, htop, d12lo, P1a, h012_2, d13hi]
      · linarith only [d12lo, htop, h013_2, h012_2, d23hi, P1a]
      · linarith only [h012_1, h123_1, htop, P1a, h013_2, P0a]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_3, h013_1, P0a, htop]
    · linarith only [htop, P0a, h012_3, h023_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, P1a, htop, P0a, h013_1, d23hi, h023_2, h123_0]
      · linarith only [P0a, h023_0, P1a, htop, d23hi, h013_2, h123_0, d12lo]
      · linarith only [htop, P1a, h013_2, P0a, h023_2]
  · linarith only [h013_0, h023_1, h123_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, d01hi, h012_1, h123_2, P0a, h023_0, htop]
    · linarith only [htop, d01hi, P0a, h123_2, d12lo, h023_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d13lo, h012_1, P1a, h023_2, d01hi]
      · linarith only [P1a, h012_1, d01hi, h123_2, d12lo, h023_1, htop]
      · linarith only [P1a, P0a, h123_1, h023_2, htop, h012_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h012_1, h013_3]
    · linarith only [d01hi, h123_2, P0a, htop, h012_0, d23lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01hi, h013_2, htop, d23lo, P1a]
      · linarith only [htop, P1a, h013_4]
      · linarith only [P0a, h123_2, htop, P1a, h012_2]
#print axioms lower_no_two_high_03

theorem lower_no_two_high_12 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, htop, P0a, h123_2, d01lo]
    · linarith only [h012_2, d01lo, htop, d13hi, P0a]
    · linarith only [h123_0, h012_2, P0a, htop]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h123_1, htop, h012_4, h123_0]
      · linarith only [h012_4, P1a, h023_2, htop]
      · linarith only [htop, P1a, h023_2, h123_1, h123_0]
    · linarith only [h023_2, d12hi, d01lo, h123_0, P0a, htop, h012_0]
    · linarith only [P0a, h023_2, h123_2, htop, h012_0]
  · linarith only [h012_1, h023_2, h123_0, h123_1]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h123_4, d02hi, P0a, d01lo, P1a]
      · linarith only [d01lo, htop, d12hi, P0a, h023_2, h123_4, P1a]
      · linarith only [h012_1, h023_2, P1a, htop]
    · linarith only [h013_2, d12hi, htop, d01lo, P0a]
    · linarith only [htop, P0a, h012_2]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d12hi, h123_0, h012_2, d23lo, htop]
    · linarith only [h013_2, d12hi, P0a, d23lo, h123_0, htop]
    · linarith only [h013_2, h012_2, P0a, htop]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, d12lo, h013_2, d13hi]
    · linarith only [d13hi, P0a, htop, d12lo, h012_2]
    · linarith only [h013_2, h012_2, htop, P0a]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h012_1, h023_1, h013_0]
  · linarith only [h013_0, h023_1, h012_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, P0a, htop, d01hi, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d12lo, h023_2, P1a, d23hi]
      · linarith only [h123_0, P1a, h012_3, d23hi, P0a, d12lo, htop]
      · linarith only [h012_3, htop, h023_2, P0a, P1a, h123_0]
    · linarith only [h013_2, P0a, h123_0, htop]
  · linarith only [h023_1, h013_0, h123_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, d12lo, P0a, h023_2, d01hi, htop, h123_1]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h023_2, d02hi, P1a, d12lo]
      · linarith only [d12lo, h123_2, P1a, d02hi, htop]
      · linarith only [P1a, h023_2, htop, h123_2]
    · linarith only [h023_2, P0a, h012_1, htop, h123_2]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, h012_2, P0a, d23lo, h123_0, htop]
    · linarith only [P0a, d01hi, h123_2, htop, d23lo]
    · linarith only [h013_2, P0a, htop]
#print axioms lower_no_two_high_12

theorem lower_no_two_high_13 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, h123_2, P0a, d23hi]
    · linarith only [d13hi, d01lo, P0a, htop, h012_2]
    · linarith only [h123_0, P0a, h012_2, htop]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P0a, P1a, d23hi, h013_4, d01lo, htop]
      · linarith only [P1a, h012_4, h123_1, h023_2, htop]
      · linarith only [h013_3, htop, P0a, P1a]
    · linarith only [P0a, d01lo, h023_2, d12hi, h012_0, htop, h123_0]
    · linarith only [h123_2, htop, h023_2, P0a, h012_0]
  · linarith only [h123_0, h012_1, h123_1, h023_2]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d03hi, P1a, h123_4, P0a, d01lo]
      · linarith only [htop, P1a, h023_0, h123_4]
      · linarith only [P0a, d02hi, P1a, d01lo, h023_2, htop]
    · linarith only [d01lo, P0a, h013_2, d12hi, htop]
    · linarith only [P0a, htop, h012_2]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, d23lo, htop, d12hi, h123_0, P0a]
    · linarith only [P0a, h013_2, htop, d12hi, d23lo, h123_0]
    · linarith only [htop, P0a, h013_2, h012_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_2, d12lo, P0a, htop, d13hi]
    · linarith only [d12lo, d13hi, h012_2, P0a, htop]
    · linarith only [h013_2, h012_2, htop, P0a]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h013_0, h023_1, h012_1]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_2, d01hi, htop, d12lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h013_4]
      · linarith only [htop, P1a, P0a, d12lo, h123_0, d23hi, h023_0, h012_3]
      · linarith only [h012_3, htop, P0a, h023_2, P1a]
    · linarith only [P0a, h013_2, htop, h123_0]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_1, P0a, d12lo, h023_2, htop, h012_1, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, d02hi, htop, h023_2, d13lo]
      · linarith only [P1a, d12lo, h123_2, htop, d03hi]
      · linarith only [P0a, htop, P1a, h023_0, h123_2, d01hi, d12lo]
    · linarith only [h012_1, htop, h123_2, h023_2, P0a]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, d01hi, h012_2, d23lo, h123_0]
    · linarith only [h123_2, d23lo, d01hi, htop, P0a]
    · linarith only [P0a, h013_2, htop]
#print axioms lower_no_two_high_13

theorem lower_no_two_high_23 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, htop, d01lo, P0a, h123_2, h012_0]
    · linarith only [h012_2, P0a, d23hi, htop, d01lo]
    · linarith only [P0a, h123_2, htop, h012_1]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h123_2, h012_0, d01lo, d12hi]
    · linarith only [d12hi, htop, h023_2, P0a, h012_0, d01lo]
    · linarith only [P0a, h023_2, htop, h123_2]
  · linarith only [h123_1, h123_0, h012_1, h023_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h023_4, P1a]
      · linarith only [h013_0, h012_3, d23lo, htop, d13hi, P0a, P1a]
      · linarith only [P1a, P0a, h013_2, htop, h012_3]
    · linarith only [d23lo, d12hi, P0a, h023_2, htop]
    · linarith only [h012_1, h023_2, htop, P0a]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, d23lo, d01hi, htop, P1a]
      · linarith only [h123_3, h012_1, d23lo, P0a, d03hi, P1a, htop]
      · linarith only [h013_0, h123_3, h012_1, P1a, htop, P0a]
    · linarith only [h013_2, P0a, d23lo, d12hi, h012_0, h123_0, htop]
    · linarith only [h123_0, htop, P0a, h013_2, h012_2]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, P0a, h012_1, d12lo, htop, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h012_2, d13hi, h013_0, d12lo, htop]
      · linarith only [P1a, d12lo, h012_2, d23hi, h013_2, htop]
      · linarith only [P0a, htop, P1a, h023_3]
    · linarith only [h013_2, h123_1, P0a, h012_2, htop]
  · linarith only [h013_2, h123_1, h012_2]
  · linarith only [h023_1, h012_1, h013_0]
  · linarith only [h013_0, h012_1, h023_1]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, h023_2, d12lo, P0a, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_4, htop, P1a]
      · linarith only [h013_0, h123_4, htop, P1a]
      · linarith only [h012_3, P0a, htop, h013_2, P1a]
    · linarith only [P0a, htop, h023_2, h012_0]
  · linarith only [h013_0, h123_0, h023_1]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, P0a, h023_2, d12lo, htop, h012_1]
    · linarith only [htop, d12lo, h123_2, h012_1, d01hi, P0a]
    · linarith only [h023_2, htop, h123_2, P0a]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, d23lo, h012_2, htop, P0a]
    · linarith only [h123_2, P0a, d23lo, htop, d02hi]
    · linarith only [h123_2, h012_0, P0a, htop]
#print axioms lower_no_two_high_23

theorem lower_no_high_middle_middle_012 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : Middle n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, d01lo, d23hi, htop, h012_1, P0a]
    · linarith only [h012_0, h013_3, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P0a, htop, h123_2, h023_4, P1a]
      · linarith only [h123_1, htop, P0a, h012_2, h023_4, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h023_4, h012_0, h123_2, htop, P2a]
        · linarith only [P0a, P2a, h023_4, h012_2, htop]
        · linarith only [P0a, h123_2, P2a, h023_0, h012_2, htop]
        · linarith only [htop, P2a, h012_0, h123_0, P1a]
        · linarith only [htop, h123_0, P2a, h012_0, P1a]
        · linarith only [P0a, h023_0, P2c, h012_2, htop]
      · linarith only [P1c, h023_4, h123_1, P0a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_0, htop, P1b, h123_0, P2a]
        · linarith only [P2a, d23hi, d01lo, htop, P1a]
        · linarith only [P0a, h123_2, P2a, htop, h023_0, P1a]
        · linarith only [h023_4, P0a, htop, h012_0, P2c]
        · linarith only [htop, h123_2, P2c]
        · linarith only [h023_0, P1a, htop, P2c, P0a]
      · linarith only [htop, P1c, h012_2]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, d12hi, h023_2, h123_2, htop, P0a]
    · linarith only [htop, h013_3, P0a, h012_0]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h123_2, h012_4, P2a]
        · linarith only [P2a, h012_4, h023_2, htop]
        · linarith only [h123_2, htop, P2a, h023_2]
        · linarith only [htop, P2c, h012_4]
        · linarith only [P2b, h023_0, P1a, htop, h123_1, P0a]
        · linarith only [h023_0, P1a, P2b, P0a, htop, h123_1]
      · linarith only [htop, h023_2, P1a, h123_0, h012_4]
      · linarith only [h023_2, h012_0, htop, P1a, h123_2]
      · linarith only [h023_0, htop, h012_4, P0a, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_0, h123_1, P2a, h123_0, htop, P1b]
        · linarith only [htop, P1b, P2a, h012_0, h023_2]
        · linarith only [P2a, h123_2, htop, h023_2]
        · linarith only [h012_0, P1b, htop, P2c]
        · linarith only [h123_2, htop, P2c]
        · linarith only [h023_2, P2c, htop]
      · linarith only [P1c, htop, h012_0, h123_0, h023_2]
  · linarith only [h123_1, h012_1, h123_0, h023_2]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop]
    · linarith only [h012_3, h013_0, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, P0a, P1a, h023_2, h123_4]
      · linarith only [d12hi, h013_2, P1a, d23lo, h023_2, P0a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, P0a, h123_4, htop, h013_2]
        · linarith only [h012_0, P2a, P1a, htop, hn]
        · linarith only [h123_1, h013_2, h023_2, htop, P2a, P0a]
        · linarith only [h012_0, htop, P1a, P2b]
        · linarith only [h013_2, P0a, P2c, htop, h123_1]
        · linarith only [htop, P2a, h012_0, P1a]
      · linarith only [P1c, htop, P0a, d12hi, d23lo, h023_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, P0a, h123_1, d23lo, d12hi, P1a, htop]
        · linarith only [h012_0, P2a, P1b, htop]
        · linarith only [htop, P1a, P0a, h023_2, P2a, h123_1]
        · linarith only [P2c, htop, h123_4, P1c]
        · linarith only [h123_1, htop, P1a, P2c, P0a]
        · linarith only [h023_2, htop, P2c]
      · linarith only [htop, P1c, h013_2]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, d12hi, htop, h123_0, h013_0, P0a, d23lo]
    · linarith only [P0a, h013_2, h123_0, htop, d23lo, d02hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_2, P1a, htop, h123_3]
      · linarith only [htop, h013_2, h123_3, P1a]
      · linarith only [htop, P1a, h013_2, h012_2]
      · linarith only [htop, h123_3, P1c]
      · linarith only [htop, h012_2, P1c]
      · linarith only [h013_2, htop, P1c]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_0, htop, h013_2, P0a, d12lo, d13hi]
    · linarith only [d03hi, htop, P0a, d12lo, h012_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_3, h013_2, P1a, htop]
      · linarith only [htop, h012_2, P1a, h123_3]
      · linarith only [htop, h012_2, P1a, h013_2]
      · linarith only [h123_3, P1c, htop]
      · linarith only [h013_2, P1c, htop]
      · linarith only [h012_2, htop, P1c]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h012_1, h023_1, h013_0]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_3, htop, h013_1, P0a]
    · linarith only [h012_3, h023_0, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_2, P0a, htop, h013_2, d12lo, d23hi, P1a]
      · linarith only [htop, h023_2, P0a, h123_4, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, htop, h012_1, P2a, hn]
        · linarith only [h123_4, P0a, P2a, h013_2, htop]
        · linarith only [h013_2, h023_2, P0a, h123_0, P2a, htop]
        · linarith only [h023_0, htop, P1a, h013_1, P2a]
        · linarith only [P1a, P2a, h013_1, htop, h023_0]
        · linarith only [P0a, htop, h123_0, h013_2, P2c]
      · linarith only [h023_2, P1c, d23hi, htop, d12lo, P0a]
      · linarith only [htop, h013_2, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, htop, h012_1, P1b]
        · linarith only [h123_4, P0a, htop, P1a, P2a]
        · linarith only [htop, h123_0, P1a, P0a, P2a, h023_2]
        · linarith only [P2c, htop, h123_4, P1c]
        · linarith only [htop, P2c, h023_2]
        · linarith only [h123_0, P2c, htop, P1a, P0a]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, d01hi, h012_1, P0a, h023_0, d12lo]
    · linarith only [d12lo, h023_2, P0a, htop, d01hi, h123_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_4, h123_1, h023_2, htop, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, h012_4, htop, P2a]
        · linarith only [h123_2, h012_4, P2a, htop]
        · linarith only [h023_2, P2a, htop, h123_2]
        · linarith only [h012_4, P2c, htop]
        · linarith only [P0a, P2b, htop, h123_0, P1a, h023_1]
        · linarith only [h123_0, P0a, h023_1, P1a, P2b, htop]
      · linarith only [h023_2, P1a, htop, h012_1, h123_2]
      · linarith only [P0a, htop, P1c, h023_1, h012_4]
      · linarith only [P1c, h023_2, h123_1, h012_1, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h012_1, h023_0, h023_1, P1b, P2a]
        · linarith only [htop, P2a, h012_1, h123_2, P1b]
        · linarith only [h123_2, htop, P2a, h023_2]
        · linarith only [P2c, P1b, h012_1, htop]
        · linarith only [h023_2, htop, P2c]
        · linarith only [htop, h123_2, P2c]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_3, h012_1]
    · linarith only [d01hi, h012_0, d23lo, P0a, h123_2, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_2, P1a, P0a, htop, h023_4, h123_0]
      · linarith only [h023_4, P0a, htop, P1a, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, htop, h023_4, h012_2, P2a]
        · linarith only [h023_4, P0a, h123_2, htop, h012_1, P2a]
        · linarith only [h023_1, P0a, htop, h012_2, P2a, h123_2]
        · linarith only [h123_1, P2b, h012_1, htop, P1a]
        · linarith only [P2c, P0a, h023_1, htop, h012_2]
        · linarith only [P1a, P2a, h123_1, h012_1, htop]
      · linarith only [P0a, P1c, h023_4, htop, h123_0]
      · linarith only [P1c, h012_2, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d01hi, htop, d23lo, P1a, P2a]
        · linarith only [htop, P1b, h012_1, P2a, h123_1]
        · linarith only [P2a, P1a, P0a, h023_1, h123_2, htop]
        · linarith only [htop, P2c, P0a, h023_4, h012_1]
        · linarith only [h023_1, P0a, P2c, P1a, htop]
        · linarith only [htop, P2c, h123_2]
#print axioms lower_no_high_middle_middle_012

theorem lower_no_high_middle_middle_013 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : Middle n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d23hi, htop, d01lo, h012_1, h123_2]
    · linarith only [P0a, h012_0, htop, h013_3]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P0a, h123_2, htop, P1a, h023_4]
      · linarith only [P1a, P0a, h023_4, htop, h123_1, h012_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [hn, P2a, htop, h012_0, P1a, h023_0]
        · linarith only [h123_0, h012_2, h023_4, P0a, P2a, htop]
        · linarith only [h123_2, htop, P0a, h012_2, P2a]
        · linarith only [h012_0, htop, P2a, P1a, h023_0]
        · linarith only [h023_0, h012_0, P2a, P1a, htop]
        · linarith only [h123_0, P2c, h012_2, htop, P0a]
      · linarith only [htop, h123_1, P1c, h023_4, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h013_0, P1b, P2a]
        · linarith only [P2a, h123_0, htop, d01lo, d23hi, P1a]
        · linarith only [h123_2, P0a, P1a, P2a, htop]
        · linarith only [P2c, htop, h023_4]
        · linarith only [P1c, htop, h123_2, P2c]
        · linarith only [P2c, P1a, h123_0, P0a, htop]
      · linarith only [htop, P1c, h012_2]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h123_2, h023_2, d12hi, htop, d01lo]
    · linarith only [h012_0, htop, P0a, h013_3]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, h023_0, h123_2, htop, P2a]
        · linarith only [P2a, h012_4, h123_1, htop, h023_2]
        · linarith only [P2a, htop, P1a, P0a, hn]
        · linarith only [h123_1, h012_4, htop, h023_0, P2c]
        · linarith only [P2b, P0a, htop, P1a]
        · linarith only [P0a, htop, P2b, P1a]
      · linarith only [h023_2, h012_4, P1a, htop, h123_0]
      · linarith only [h123_2, h012_0, htop, P1a, h023_2]
      · linarith only [htop, P0a, P1c, h023_0, h012_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h012_0, htop, P1b, h123_0, h123_1, h023_0]
        · linarith only [h123_1, htop, h012_0, P2a, P1b, h023_2]
        · linarith only [P0a, htop, P2a, P1a]
        · linarith only [P1b, h012_0, P2c, htop, h123_1, h023_0]
        · linarith only [P1c, htop, h123_2, P2c]
        · linarith only [h012_0, P2c, htop, h023_2, P0a]
      · linarith only [h023_2, htop, h123_0, P1c, h012_0]
  · linarith only [h123_0, h023_2, h123_1, h012_1]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_3, P0a]
    · linarith only [h012_3, h013_0, htop, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_2, h123_4, htop, P1a, P0a]
      · linarith only [htop, d23lo, h013_2, P1a, h023_2, P0a, d12hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h013_2, h023_1, P0a, h123_4, htop]
        · linarith only [P0a, htop, h123_4, h023_2, P2a, h013_0]
        · linarith only [h023_2, h013_2, P0a, htop, P2a]
        · linarith only [h013_0, h123_1, P1a, htop, P2b]
        · linarith only [h013_2, h023_1, htop, P0a, P2c]
        · linarith only [h123_1, htop, h013_0, P2a, P1a]
      · linarith only [h023_2, P1c, P0a, d23lo, d12hi, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, d12hi, P1a, h023_1, d23lo, P2a, P0a, h123_1]
        · linarith only [h013_0, htop, P1b, h123_1, P2a]
        · linarith only [P1a, htop, h023_2, P2a, P0a]
        · linarith only [htop, h123_4, P2c]
        · linarith only [P1a, htop, h023_1, P2c, P0a]
        · linarith only [P2c, P0a, h013_0, htop, h023_2]
      · linarith only [P1c, htop, h013_2]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_0, h012_2, d23lo, P0a, h013_0, d12hi]
    · linarith only [h013_2, d02hi, d23lo, h123_0, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, P1a, h012_2, h123_3]
      · linarith only [htop, P1a, h013_2, h123_3]
      · linarith only [h012_2, h013_2, htop, P1a]
      · linarith only [htop, P1c, h123_3]
      · linarith only [P1c, h012_2, htop]
      · linarith only [htop, h013_2, P1c]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, htop, h012_0, d13hi, P0a, h013_2]
    · linarith only [d03hi, htop, d12lo, P0a, h012_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_3, h013_2, P1a, htop]
      · linarith only [h012_2, htop, h123_3, P1a]
      · linarith only [h013_2, P1a, htop, h012_2]
      · linarith only [h123_3, htop, P1c]
      · linarith only [P1c, htop, h013_2]
      · linarith only [P1c, htop, h012_2]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h013_1, h012_3]
    · linarith only [htop, P0a, h012_3, h023_0]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, d12lo, h023_2, P0a, P1a, d23hi, h013_2]
      · linarith only [h023_2, P1a, P0a, h123_4, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_4, P2a, h013_1, htop, P0a, h023_2]
        · linarith only [h123_4, h013_2, htop, P0a, h023_0, P2a]
        · linarith only [P0a, h023_2, htop, h013_2, P2a]
        · linarith only [htop, h123_0, P2a, P1a, h013_1]
        · linarith only [P2a, P1a, htop, h123_0, h013_1]
        · linarith only [h013_2, P0a, htop, P2c, h023_0]
      · linarith only [htop, P1c, d23hi, d12lo, h023_2, P0a]
      · linarith only [h013_2, htop, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1b, h123_0, P2a, h013_1, htop]
        · linarith only [P1a, h023_0, P0a, P2a, htop, h123_4]
        · linarith only [P0a, h023_2, htop, P1a, P2a]
        · linarith only [htop, h123_4, P2c]
        · linarith only [P2c, htop, h023_2, P0a, h013_1]
        · linarith only [P2c, P1a, P0a, h023_0, htop]
  · linarith only [h013_0, h023_1, h123_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, d12lo, d01hi, P0a, h012_1, h023_0]
    · linarith only [d01hi, htop, h123_2, d12lo, P0a, h023_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_2, P1a, htop, h123_1, h012_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, h023_2, P2a, htop, h123_0]
        · linarith only [h123_2, htop, h012_4, h023_1, P2a]
        · linarith only [htop, P0a, P2a, P1a, hn]
        · linarith only [h123_0, P2c, h023_1, htop, h012_4]
        · linarith only [P0a, P1a, htop, P2b]
        · linarith only [P2b, P1a, htop, P0a]
      · linarith only [h012_1, P1a, htop, h023_2, h123_2]
      · linarith only [P0a, htop, h023_1, h012_4, P1c]
      · linarith only [h023_2, htop, h123_1, P1c, h012_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, htop, P2a, h012_1, P1b, h123_0]
        · linarith only [P2a, htop, h023_1, h123_2, P1b, h012_1]
        · linarith only [htop, P0a, P2a, P1a]
        · linarith only [h012_1, P2c, P1b, h023_1, htop, h123_0]
        · linarith only [P0a, h023_2, P2c, htop, h012_1]
        · linarith only [P2c, P1c, h123_2, htop]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, P0a, h012_1, htop]
    · linarith only [P0a, d01hi, htop, h012_0, d23lo, h123_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P0a, htop, h123_0, P1a, h023_4, h012_2]
      · linarith only [htop, P1a, h123_2, h023_4, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_4, P2a, htop, P0a, h012_2, h123_1]
        · linarith only [h023_1, P1a, htop, P2a, h012_1, hn]
        · linarith only [h123_2, P2a, P0a, htop, h012_2]
        · linarith only [P2b, htop, h012_1, P1a, h023_1]
        · linarith only [P2c, P0a, h012_2, h123_1, htop]
        · linarith only [htop, P1a, P2a, h023_1, h012_1]
      · linarith only [P1c, P0a, h023_4, htop, h123_0]
      · linarith only [h012_2, htop, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, h123_1, P2a, d01hi, d23lo, htop]
        · linarith only [h023_1, h012_1, P2a, P1b, htop]
        · linarith only [P2a, P1a, P0a, htop, h123_2]
        · linarith only [P2c, htop, h023_4]
        · linarith only [P0a, P2c, h123_1, P1a, htop]
        · linarith only [htop, h123_2, P2c, P1c]
#print axioms lower_no_high_middle_middle_013

theorem lower_no_high_middle_middle_023 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : Middle n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d23hi, d01lo, P0a, h123_2, h012_1]
    · linarith only [htop, h012_0, h013_3, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_2, htop, P0a, h012_0, h023_4, P1a]
      · linarith only [h023_4, P0a, htop, h012_2, P1a]
      · linarith only [h123_2, h023_0, h012_2, P0a, htop, P1a]
      · linarith only [h012_0, P1c, h023_4, htop, P0a]
      · linarith only [h123_2, htop, P1c]
      · linarith only [htop, P0a, P1c, h012_2, h023_0]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, d01lo, htop, h123_2, d12hi, P0a]
    · linarith only [h013_3, htop, h012_0, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_2, htop, P1a, h012_4]
      · linarith only [P1a, h023_2, h012_4, htop]
      · linarith only [h023_2, h123_2, P1a, htop]
      · linarith only [htop, h012_4, P1c]
      · linarith only [P1c, htop, h123_2]
      · linarith only [P1c, htop, h023_2]
  · linarith only [h023_2, h123_1, h012_1, h123_0]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop]
    · linarith only [htop, h013_0, P0a, h012_3]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_2, htop, h123_4, P0a, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d23lo, hn, htop, P1a, P2a, h023_1, d12hi]
        · linarith only [htop, h123_4, h023_2, h013_0, P0a, P2a]
        · linarith only [P2a, h013_2, h023_2, P0a, htop]
        · linarith only [d23lo, htop, d12hi, P2a, P1a, h023_1]
        · linarith only [P1a, h023_1, P2a, htop, d12hi, d23lo]
        · linarith only [h013_0, P2c, P0a, htop, h023_2]
      · linarith only [h023_2, P0a, h123_1, htop, P1a, h013_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d23lo, P2a, h023_1, htop, P1b, d12hi]
        · linarith only [h013_0, P1a, P0a, d23lo, P2a, htop, d13hi]
        · linarith only [P0a, P1a, htop, P2a, h013_2]
        · linarith only [P2c, h123_4, htop]
        · linarith only [P0a, h013_2, h023_1, htop, P2c]
        · linarith only [htop, P1a, h013_0, P2c, P0a]
      · linarith only [h013_2, h123_1, P0a, P1c, htop]
      · linarith only [P1c, htop, h023_2]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_0, d23lo, h012_2, d12hi, htop, P0a, h123_0]
    · linarith only [htop, h123_0, d23lo, d02hi, P0a, h013_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h012_2, d12hi, htop, d23lo, h013_2]
        · linarith only [htop, h013_1, P2a, h123_3, h012_2]
        · linarith only [htop, P1a, P0a, hn, P2a]
        · linarith only [d23lo, P2c, h012_2, h013_1, htop, d12hi]
        · linarith only [P2b, P1a, htop, P0a]
        · linarith only [P2b, P1a, P0a, htop]
      · linarith only [P1a, htop, h012_0, h123_3, h013_2]
      · linarith only [h123_0, P1a, h012_2, htop, h013_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1b, h012_0, d12hi, htop, h013_0, d23lo, h013_1, P2a]
        · linarith only [P2a, h013_1, h012_0, htop, P1b, h123_3]
        · linarith only [P1a, P0a, P2a, htop]
        · linarith only [h012_0, htop, d12hi, P1b, d23lo, h013_1, P2c]
        · linarith only [h013_2, h012_0, htop, P2c, P0a]
        · linarith only [P1c, htop, h123_3, P2c]
      · linarith only [h012_2, htop, P0a, h013_1, P1c]
      · linarith only [h013_2, h123_0, P1c, h012_0, htop]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, P0a, h012_0, htop, d13hi, h013_2]
    · linarith only [d12lo, P0a, d03hi, h012_2, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h012_1, h123_3, P1a, h013_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_0, h123_3, htop, P2a, h012_2]
        · linarith only [htop, d12lo, P2a, d23hi, h013_2, h012_2]
        · linarith only [htop, P2a, P0a, hn, P1a]
        · linarith only [P2c, h013_0, h012_2, d23hi, htop, d12lo]
        · linarith only [P1a, htop, P0a, P2b]
        · linarith only [P0a, P2b, P1a, htop]
      · linarith only [htop, h123_1, h012_2, h013_2, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_0, d13hi, P1a, d12lo, h012_1, htop, P2a]
        · linarith only [h012_1, P2a, h013_2, htop, d23hi, d12lo, P1a]
        · linarith only [htop, P1b, P2a, P0a]
        · linarith only [d12lo, h012_1, P2c, htop, P1a, h013_0, d23hi]
        · linarith only [h123_3, htop, P2c, P1c]
        · linarith only [P0a, h012_1, htop, h013_2, P2c]
      · linarith only [h013_2, htop, h012_1, h123_1, P1c]
      · linarith only [h012_2, P1c, P0a, htop, h013_0]
  · linarith only [h013_2, h012_2, h123_1]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h012_3, h013_1]
    · linarith only [htop, h023_0, P0a, h012_3]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h023_2, h013_1, P0a, h123_4, htop]
        · linarith only [P2a, h023_0, htop, d23hi, P1a, d12lo, hn]
        · linarith only [h023_2, P2a, P0a, htop, h013_2]
        · linarith only [P2b, h023_0, d12lo, P1a, htop, d23hi]
        · linarith only [h023_2, htop, h013_1, P0a, P2c]
        · linarith only [d23hi, d12lo, h023_0, P1a, P2a, htop]
      · linarith only [P1a, h013_2, P0a, htop, h123_4]
      · linarith only [h013_2, P0a, h023_2, h123_0, htop, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h123_4, P2a, P1b, P0a, h013_1]
        · linarith only [P2a, d12lo, d23hi, P1a, htop, h023_0]
        · linarith only [P0a, P2a, P1b, htop, h013_2]
        · linarith only [P2c, h123_4, htop]
        · linarith only [P1b, P2c, P0a, htop, h013_1]
        · linarith only [htop, h013_2, P0a, h023_0, P2c]
      · linarith only [htop, P1c, h023_2]
      · linarith only [htop, h013_2, h123_0, P0a, P1c]
  · linarith only [h013_0, h023_1, h123_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, h023_0, d12lo, P0a, h012_1, d01hi]
    · linarith only [h123_2, h023_2, d12lo, d01hi, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h012_4, h023_2, htop]
      · linarith only [htop, h012_4, P1a, h123_2]
      · linarith only [P1a, h123_2, htop, h023_2]
      · linarith only [h012_4, htop, P1c]
      · linarith only [htop, h023_2, P1c]
      · linarith only [h123_2, P1c, htop]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop, h012_1]
    · linarith only [h123_2, P0a, h012_0, d23lo, htop, d01hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h012_2, h023_4, P0a, P1a]
      · linarith only [h123_2, P1a, htop, P0a, h012_1, h023_4]
      · linarith only [P1a, P0a, h123_2, h023_1, htop, h012_2]
      · linarith only [htop, P0a, P1c, h023_4, h012_1]
      · linarith only [h012_2, P1c, htop, h023_1, P0a]
      · linarith only [P1c, htop, h123_2]
#print axioms lower_no_high_middle_middle_023

theorem lower_no_high_middle_middle_102 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d23hi, P0a, d01lo, h123_2]
    · linarith only [h012_2, d01lo, d13hi, htop, P0a]
    · linarith only [htop, h123_0, h012_2, P0a]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_2, h123_2, P1a, d01lo, htop, d12hi]
      · linarith only [h123_1, htop, h012_4, h013_3, P1a, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h012_4, htop, h123_2]
        · linarith only [P2a, h012_4, htop, h023_2]
        · linarith only [P2a, htop, h023_2, h123_2]
        · linarith only [P2c, htop, h012_4]
        · linarith only [P1a, h123_1, htop, P0a, h023_0, P2b]
        · linarith only [htop, h123_1, P2b, P1a, h023_0, P0a]
      · linarith only [h123_2, d12hi, d01lo, htop, h023_1, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, d01lo, h123_2, d12hi, htop, P1a]
        · linarith only [htop, d01lo, P1a, h023_2, P2a, d12hi]
        · linarith only [h123_2, h023_2, htop, P2a]
        · linarith only [P1a, P2c, d12hi, htop, d01lo]
        · linarith only [h123_2, P2c, htop]
        · linarith only [h023_2, htop, P2c]
      · linarith only [h123_1, P0a, h012_4, htop, P1c]
    · linarith only [d12hi, h012_0, d01lo, h023_2, h123_0, P0a, htop]
    · linarith only [htop, h023_2, P0a, h012_0, h123_2]
  · linarith only [h123_0, h123_1, h023_2, h012_1]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h123_4, h012_3, htop, P2a]
        · linarith only [P1a, h023_1, d12hi, hn, P2a, d01lo, htop]
        · linarith only [P0a, P2a, h123_1, h023_2, h012_3, htop]
        · linarith only [P1a, htop, d01lo, P2b, h023_1, d12hi]
        · linarith only [P2c, P0a, h012_3, htop, h123_1]
        · linarith only [htop, h023_1, d12hi, P2a, P1a, d01lo]
      · linarith only [P0a, h012_3, h123_4, htop, P1a, h023_0]
      · linarith only [h023_2, htop, P1a, h123_4, P0a]
      · linarith only [htop, P1c, h012_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P0a, h123_4, P2a, P1b]
        · linarith only [P1a, P2a, h023_1, d01lo, d12hi, htop]
        · linarith only [P0a, h023_1, P1b, htop, h023_0, P2a, h123_1]
        · linarith only [P0a, htop, d12hi, P2c, h123_4, d01lo]
        · linarith only [htop, P0a, h123_1, P1b, P2c]
        · linarith only [htop, h023_2, P2c]
      · linarith only [htop, h023_0, h123_4, P0a, P1c]
    · linarith only [d01lo, h013_2, d12hi, htop, P0a]
    · linarith only [h012_2, htop, P0a]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h123_0, h012_2, h013_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, P0a, d12hi, h012_2, h123_0, htop]
    · linarith only [P0a, d23lo, h123_0, h013_2, d12hi, htop]
    · linarith only [htop, h012_2, P0a, h013_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, P0a, d12lo, h013_2, htop]
    · linarith only [h012_2, htop, d13hi, P0a, d12lo]
    · linarith only [h012_2, h013_2, P0a, htop]
  · linarith only [h012_2, h013_2, h123_1]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, d01hi, h013_2, d12lo]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_4, P1a, htop, h012_3, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_4, htop, P0a, d01hi, d12lo, P2a, h023_2]
        · linarith only [P2a, P0a, h123_4, htop, h012_3]
        · linarith only [h023_2, P2a, h012_3, htop, P0a, h123_0]
        · linarith only [d01hi, P2a, P1a, d12lo, h023_0, htop]
        · linarith only [d01hi, htop, d12lo, P1a, h023_0, P2a]
        · linarith only [h012_3, htop, P2c, h123_0, P0a]
      · linarith only [h023_2, P1a, h123_4, P0a, htop]
      · linarith only [htop, P1c, h012_3]
      · linarith only [P1c, h023_1, h123_4, P0a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, d12lo, P2a, htop, d01hi, h023_0]
        · linarith only [h123_0, d23hi, P2a, P1b, P0a, d12lo, htop]
        · linarith only [h023_2, P1b, P2a, P0a, htop, h123_0]
        · linarith only [htop, h123_4, P0a, d01hi, d12lo, P2c]
        · linarith only [P2c, htop, h023_2]
        · linarith only [h123_0, P0a, P1b, P2c, htop]
    · linarith only [P0a, htop, h013_2, h123_0]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, htop, h023_2, d01hi, P0a, h012_1, h123_1]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_0, P1a, h123_2, htop, h012_4]
      · linarith only [h123_2, P1a, h023_2, htop, d12lo, d01hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, htop, P2a, h023_2]
        · linarith only [htop, P2a, h123_2, h012_4]
        · linarith only [h123_0, htop, h023_1, P1a, P0a, hn, P2a]
        · linarith only [h012_4, P2c, htop]
        · linarith only [P0a, P2b, h123_0, h023_1, htop, P1a]
        · linarith only [P1a, P0a, h123_0, htop, P2b, h023_1]
      · linarith only [h023_0, d12lo, d01hi, h123_2, htop, P1c]
      · linarith only [htop, P1c, h123_0, P0a, h012_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d12lo, htop, P1a, P2a, d01hi, h023_2]
        · linarith only [d01hi, d12lo, htop, P2a, P1a, h123_2]
        · linarith only [P2a, htop, h123_2, h023_2]
        · linarith only [P1a, P2c, d12lo, d01hi, htop]
        · linarith only [P2c, h023_2, htop]
        · linarith only [P2c, h123_2, htop]
    · linarith only [h012_1, h123_2, htop, h023_2, P0a]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_0, P0a, d01hi, h012_2, d23lo]
    · linarith only [P0a, h123_2, d01hi, htop, d23lo]
    · linarith only [P0a, htop, h013_2]
#print axioms lower_no_high_middle_middle_102

theorem lower_no_high_middle_middle_103 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, d01lo, d23hi, P0a]
    · linarith only [d01lo, P0a, htop, h012_2, d13hi]
    · linarith only [P0a, htop, h012_2, h123_0]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h023_2, htop, d12hi, h123_2, d01lo]
      · linarith only [h013_3, htop, P1a, h012_4, P0a, h123_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_2, h023_0, h012_4, htop]
        · linarith only [h012_4, h023_2, htop, h123_1, P2a]
        · linarith only [P2a, htop, P0a, P1a, hn]
        · linarith only [h012_4, P2c, htop, h023_0, h123_1]
        · linarith only [htop, P2b, P1a, P0a]
        · linarith only [P2b, htop, P1a, P0a]
      · linarith only [h123_2, htop, h023_1, P1c, d12hi, d01lo]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P1a, h023_0, d12hi, d01lo, h123_2, P2a]
        · linarith only [h023_2, d01lo, d13hi, P1a, htop, P2a]
        · linarith only [P1b, P0a, htop, P2a]
        · linarith only [htop, P1a, d12hi, P2c, h123_1, h023_0, d01lo]
        · linarith only [d01lo, P2c, P0a, h123_2, htop, d12hi]
        · linarith only [h023_2, htop, P1c, P2c]
      · linarith only [h123_1, P0a, h012_4, P1c, htop]
    · linarith only [htop, h123_0, P0a, d01lo, h012_0, d12hi, h023_2]
    · linarith only [h123_2, h023_2, htop, h012_0, P0a]
  · linarith only [h023_2, h123_1, h012_1, h123_0]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_4, h012_3, htop, h023_1, P2a, P0a]
        · linarith only [d01lo, h123_1, d12hi, P1a, htop, P2a, hn]
        · linarith only [htop, P0a, h012_3, P2a, h023_2]
        · linarith only [h123_1, P2b, d01lo, P1a, htop, d12hi]
        · linarith only [P0a, h023_1, htop, P2c, h012_3]
        · linarith only [htop, P1a, d12hi, h123_1, P2a, d01lo]
      · linarith only [h023_0, P0a, htop, P1a, h012_3, h123_4]
      · linarith only [h123_4, P0a, htop, h023_2, P1a]
      · linarith only [h012_3, P1c, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, htop, P1b, P2a, h023_1, h123_4]
        · linarith only [h123_1, d12hi, d01lo, P2a, P1a, htop]
        · linarith only [h023_0, P0a, P2a, P1b, h023_1, htop]
        · linarith only [P2c, h123_4, htop]
        · linarith only [P0a, P1b, h023_1, htop, P2c]
        · linarith only [P1c, P2c, htop, h023_2]
      · linarith only [P1c, h123_4, P0a, h023_0, htop]
    · linarith only [d01lo, h013_2, P0a, d12hi, htop]
    · linarith only [P0a, htop, h012_2]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h123_0, h012_2, h013_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, h012_2, P0a, d12hi, h123_0, htop]
    · linarith only [d12hi, d23lo, htop, P0a, h123_0, h013_2]
    · linarith only [htop, P0a, h013_2, h012_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_2, d12lo, d13hi]
    · linarith only [P0a, htop, h012_2, d13hi, d12lo]
    · linarith only [h012_2, htop, P0a, h013_2]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_2, d12lo, P0a, htop, d01hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_3, P0a, P1a, h013_4, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, h123_0, P2a, hn, htop, d12lo, d01hi]
        · linarith only [h123_4, h012_3, P2a, htop, P0a, h023_0]
        · linarith only [h023_2, h012_3, P0a, htop, P2a]
        · linarith only [d01hi, P1a, P2a, htop, d12lo, h123_0]
        · linarith only [d01hi, htop, d12lo, P2a, P1a, h123_0]
        · linarith only [P0a, P2c, h023_0, h012_3, htop]
      · linarith only [P0a, h123_4, h023_2, P1a, htop]
      · linarith only [P1c, h012_3, htop]
      · linarith only [P0a, h023_1, P1c, h123_4, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d01hi, h123_0, P1a, htop, d12lo, P2a]
        · linarith only [P2a, htop, d23hi, P1b, d12lo, h123_0, h023_0, P0a]
        · linarith only [htop, P1b, P2a, P0a, h023_2]
        · linarith only [h123_4, htop, P2c]
        · linarith only [htop, P1c, h023_2, P2c]
        · linarith only [P1b, P0a, htop, P2c, h023_0]
    · linarith only [P0a, h013_2, h123_0, htop]
  · linarith only [h023_1, h123_0, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_1, d01hi, h023_2, htop, P0a, d12lo, h012_1]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_0, h012_4, h123_2, P1a, htop]
      · linarith only [h023_2, P1a, h123_2, d12lo, htop, d01hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, h012_4, P2a, h123_0, htop]
        · linarith only [P0a, d12lo, d01hi, h123_2, h013_4, htop, P2a]
        · linarith only [P0a, hn, P2a, P1a, htop]
        · linarith only [h012_4, h123_0, P2c, h023_1, htop]
        · linarith only [htop, P0a, P2b, P1a]
        · linarith only [P2b, htop, P1a, P0a]
      · linarith only [htop, d12lo, d01hi, P1c, h023_0, h123_2]
      · linarith only [h123_0, P1c, htop, P0a, h012_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, h023_2, d01hi, d13lo, P2a, htop]
        · linarith only [P2a, htop, h023_1, h123_2, d12lo, d01hi, P1a]
        · linarith only [P0a, P2a, htop, P1b]
        · linarith only [h123_0, P2c, P1a, d01hi, htop, d12lo, h023_1]
        · linarith only [P1c, P2c, htop, h023_2]
        · linarith only [P2c, d01hi, htop, h123_2, d12lo, P0a]
    · linarith only [h023_2, h123_2, P0a, h012_1, htop]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, h123_0, d23lo, P0a, htop, h012_2]
    · linarith only [d23lo, d01hi, h123_2, P0a, htop]
    · linarith only [P0a, h013_2, htop]
#print axioms lower_no_high_middle_middle_103

theorem lower_no_high_middle_middle_123 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : Middle n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, d23hi, h123_2, P0a]
    · linarith only [h012_2, d13hi, P0a, d01lo, htop]
    · linarith only [P0a, htop, h123_0, h012_2]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_2, h012_4, htop, P1a]
      · linarith only [h012_4, htop, P1a, h023_2]
      · linarith only [P1a, h123_2, htop, h023_2]
      · linarith only [htop, P1c, h012_4]
      · linarith only [h123_2, P1c, htop]
      · linarith only [P1c, htop, h023_2]
    · linarith only [h012_0, P0a, d01lo, htop, h023_2, h123_0, d12hi]
    · linarith only [P0a, h012_0, h123_2, htop, h023_2]
  · linarith only [h123_0, h123_1, h023_2, h012_1]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_3, h123_4, P0a, P1a, htop]
      · linarith only [h123_4, d12hi, P0a, d01lo, P1a, h023_2, htop]
      · linarith only [htop, P1a, h123_1, h012_3, h023_2, P0a]
      · linarith only [d12hi, P1c, htop, h123_4, d01lo, P0a]
      · linarith only [P0a, htop, h123_1, P1c, h012_3]
      · linarith only [htop, h023_2, P1c]
    · linarith only [d01lo, htop, P0a, h013_2, d12hi]
    · linarith only [h012_2, P0a, htop]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h123_0, h013_2, h012_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d12hi, d23lo, h012_2, P0a, h123_0]
    · linarith only [htop, d23lo, h013_2, h123_0, P0a, d12hi]
    · linarith only [h012_2, htop, P0a, h013_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, d13hi, htop, h013_2, P0a]
    · linarith only [h012_2, d13hi, P0a, htop, d12lo]
    · linarith only [h013_2, h012_2, htop, P0a]
  · linarith only [h013_2, h123_1, h012_2]
  · linarith only [h013_0, h023_1, h012_1]
  · linarith only [h013_0, h023_1, h012_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d01hi, d12lo, h013_2, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, P1a, d12lo, P0a, d01hi, h023_2, h123_4]
      · linarith only [h012_3, P1a, htop, P0a, h123_4]
      · linarith only [htop, h012_3, P0a, h123_0, P1a, h023_2]
      · linarith only [P0a, d01hi, h123_4, d12lo, P1c, htop]
      · linarith only [h023_2, htop, P1c]
      · linarith only [h123_0, P1c, htop, h012_3, P0a]
    · linarith only [P0a, h013_2, htop, h123_0]
  · linarith only [h123_0, h013_0, h023_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d12lo, h023_2, d01hi, P0a, h012_1, h123_1]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, htop, h012_4, h023_2]
      · linarith only [P1a, h012_4, htop, h123_2]
      · linarith only [P1a, htop, h123_2, h023_2]
      · linarith only [h012_4, htop, P1c]
      · linarith only [htop, P1c, h023_2]
      · linarith only [htop, P1c, h123_2]
    · linarith only [P0a, h012_1, h023_2, h123_2, htop]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d01hi, P0a, d23lo, h012_2, h123_0]
    · linarith only [d01hi, d23lo, P0a, htop, h123_2]
    · linarith only [htop, P0a, h013_2]
#print axioms lower_no_high_middle_middle_123

theorem lower_no_high_middle_middle_201 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, d23hi, htop, P0a, h123_2, h012_0]
    · linarith only [d01lo, h012_2, htop, P0a, d23hi]
    · linarith only [h012_1, P0a, h123_2, htop]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d01lo, P0a, d12hi, h012_0, h123_2]
    · linarith only [d12hi, h012_0, P0a, htop, h023_2, d01lo]
    · linarith only [h023_2, htop, P0a, h123_2]
  · linarith only [h012_1, h023_2, h123_0, h123_1]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, P0a, P1a, h012_3, h023_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h012_3, htop, h123_4, P2a]
        · linarith only [P0a, h012_3, P2a, h013_2, d12hi, htop, d23lo]
        · linarith only [P0a, h012_1, P2a, h123_4, h013_2, htop]
        · linarith only [P0a, d12hi, d23lo, h012_3, P2c, htop]
        · linarith only [P2b, h012_1, htop, P1a, h013_0]
        · linarith only [htop, h012_1, h013_0, P2b, P1a]
      · linarith only [h123_4, P0a, P1a, htop, h013_2]
      · linarith only [P1c, h012_3, htop]
      · linarith only [P0a, P1c, htop, h123_4, h013_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P2a, d23lo, P1b, P0a, d13hi]
        · linarith only [P0a, P1b, P2a, d12hi, h013_2, d23lo, htop]
        · linarith only [h012_1, P2a, h013_0, htop, P1a]
        · linarith only [d12hi, P0a, P1b, P2c, htop, d23lo]
        · linarith only [h012_1, P2c, P0a, h123_4, htop]
        · linarith only [P2c, h013_2, htop]
    · linarith only [d12hi, h023_2, htop, d23lo, P0a]
    · linarith only [h012_1, htop, P0a, h023_2]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h123_0, h013_2, h012_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_0, h012_2, P1a, htop, h123_3]
      · linarith only [htop, h012_1, P1a, h013_2, h123_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h012_2, h123_3, htop]
        · linarith only [h123_3, htop, P2a, h013_2]
        · linarith only [htop, h013_2, h012_2, P2a]
        · linarith only [h013_1, d23lo, P0a, P2b, P1a, d12hi, htop]
        · linarith only [h012_2, P2c, htop]
        · linarith only [P0a, h013_1, htop, P1a, P2a, d12hi, d23lo]
      · linarith only [h123_3, P1c, htop, h013_0, h012_1]
      · linarith only [h012_2, P0a, d12hi, d23lo, P1c, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d02hi, htop, P2a, d13lo, P1a]
        · linarith only [P0a, htop, d12hi, P1b, d23lo, h013_1, P2a]
        · linarith only [h012_1, h013_2, htop, P1a, P2a]
        · linarith only [h123_3, htop, P2c]
        · linarith only [P2c, htop, h012_1, P1a]
        · linarith only [h013_2, P2c, htop]
    · linarith only [h123_0, h013_2, d12hi, h012_0, d23lo, P0a, htop]
    · linarith only [h012_2, P0a, h123_0, htop, h013_2]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, h012_1, d12lo, htop, P0a, h013_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_0, h123_3, htop, P1a, h013_2]
      · linarith only [d23hi, P1a, P0a, h023_3, htop, h012_2, d12lo]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_3, htop, h013_2]
        · linarith only [htop, h123_3, h012_2, P2a]
        · linarith only [h012_2, h013_2, htop, P2a]
        · linarith only [htop, h013_0, d12lo, P0a, d23hi, P1a, P2a]
        · linarith only [d12lo, P1a, h013_0, P0a, P2a, htop, d23hi]
        · linarith only [P2c, htop, h012_2]
      · linarith only [h012_0, htop, h123_3, P1c, h013_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, d12lo, P1b, P0a, h013_0, d23hi, P2a]
        · linarith only [htop, d13hi, P1a, P2a, d02lo]
        · linarith only [h013_2, h012_0, P2a, htop, P1a]
        · linarith only [htop, h123_3, P2c]
        · linarith only [P2c, h013_2, htop]
        · linarith only [h012_0, htop, P2c, P1a]
      · linarith only [h012_2, P0a, htop, d12lo, P1c, d23hi]
    · linarith only [P0a, h123_1, h012_2, h013_2, htop]
  · linarith only [h012_2, h123_1, h013_2]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, P0a, d23hi, d12lo, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d12lo, P0a, d23hi, h013_2, htop, h012_3, P2a]
        · linarith only [h123_4, P2a, P0a, h012_3, htop]
        · linarith only [h012_0, h013_1, P1a, htop, hn, P2a]
        · linarith only [d23hi, P2c, h012_3, htop, d12lo, P0a]
        · linarith only [htop, h013_1, P1a, P2b, h012_0]
        · linarith only [h013_1, h012_0, P1a, htop, P2b]
      · linarith only [htop, h123_4, h012_3, P0a, h013_0, P1a]
      · linarith only [P1a, htop, P0a, h123_4, h013_2]
      · linarith only [P1c, htop, h012_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h013_1, P1b, htop, P0a, d23hi, h013_0, d12lo]
        · linarith only [P0a, h123_4, P1b, htop, P2a]
        · linarith only [P2a, h012_0, P1a, htop, h013_1]
        · linarith only [P0a, d12lo, htop, P2c, P1b, d23hi]
        · linarith only [h013_2, htop, P2c]
        · linarith only [h123_4, P2c, h012_0, P0a, htop]
      · linarith only [htop, h013_0, h123_4, P0a, P1c]
    · linarith only [h012_0, P0a, h023_2, htop]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, htop, d12lo, h012_1, P0a, d01hi]
    · linarith only [h123_2, P0a, h012_1, htop, d12lo, d01hi]
    · linarith only [P0a, htop, h123_2, h023_2]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h012_2, d23lo, d01hi]
    · linarith only [d23lo, htop, d02hi, h123_2, P0a]
    · linarith only [htop, P0a, h123_2, h012_0]
#print axioms lower_no_high_middle_middle_201

theorem lower_no_high_middle_middle_203 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, h123_2, P0a, h012_0, d23hi]
    · linarith only [htop, h012_2, P0a, d01lo, d23hi]
    · linarith only [h123_2, h012_1, htop, P0a]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, h123_2, h012_0, P0a, d12hi, htop]
    · linarith only [d12hi, htop, h023_2, d01lo, P0a, h012_0]
    · linarith only [h023_2, h123_2, htop, P0a]
  · linarith only [h123_0, h012_1, h023_2, h123_1]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h023_4, P0a, h012_3, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, d23lo, hn, htop, P1a, d02hi]
        · linarith only [P0a, P2a, h012_3, htop, h123_4, h013_0]
        · linarith only [P2a, h013_2, htop, h012_3, P0a]
        · linarith only [P1a, P2a, d02hi, d23lo, htop]
        · linarith only [d23lo, d02hi, P1a, P2a, htop]
        · linarith only [h012_3, P2c, h013_0, P0a, htop]
      · linarith only [htop, h013_2, P0a, P1a, h123_4]
      · linarith only [htop, P1c, h012_3]
      · linarith only [htop, P1c, h123_4, P0a, h013_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, htop, P2a, d23lo, d02hi]
        · linarith only [h013_0, P2a, d23lo, d13hi, P0a, htop, P1b]
        · linarith only [h013_2, P1b, P0a, P2a, htop]
        · linarith only [P2c, htop, h123_4]
        · linarith only [h013_2, htop, P1c, P2c]
        · linarith only [P0a, h013_0, htop, P1b, P2c]
    · linarith only [d12hi, d23lo, htop, P0a, h023_2]
    · linarith only [h023_2, P0a, h012_1, htop]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h012_2, h123_0, h013_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h013_0, P1a, h012_2, h123_3]
      · linarith only [P1a, h013_2, htop, h012_1, h123_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, d23lo, h013_2, htop, h012_2, d12hi]
        · linarith only [h013_1, P2a, h123_3, htop, h012_2]
        · linarith only [P0a, P1a, P2a, hn, htop]
        · linarith only [htop, d12hi, h013_1, P2c, d23lo, h012_2]
        · linarith only [P0a, P1a, htop, P2b]
        · linarith only [P1a, htop, P0a, P2b]
      · linarith only [htop, h123_3, P1c, h013_0, h012_1]
      · linarith only [h012_2, P1c, P0a, htop, d12hi, d23lo]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d23lo, P1a, h013_2, d02hi, P2a, htop]
        · linarith only [h123_3, P1a, h012_1, h013_1, htop, P2a]
        · linarith only [P2a, P1b, htop, P0a]
        · linarith only [P1a, h012_1, P2c, d23lo, d12hi, htop, h013_1]
        · linarith only [h013_2, htop, P2c, P1c]
        · linarith only [h123_3, P2c, P0a, h012_1, htop]
    · linarith only [htop, d23lo, h012_0, h123_0, d12hi, P0a, h013_2]
    · linarith only [h012_2, htop, P0a, h123_0, h013_2]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d13hi, P0a, h013_2, h012_1, d12lo]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h013_2, h012_0, P1a, h123_3]
      · linarith only [d23hi, h023_3, P1a, P0a, h012_2, d12lo, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P2a, h123_3, h012_2, h013_0]
        · linarith only [h013_2, P2a, h012_2, htop, d23hi, d12lo]
        · linarith only [P0a, P1a, htop, P2a, hn]
        · linarith only [P2c, d12lo, h013_0, h012_2, d23hi, htop]
        · linarith only [P0a, P2b, htop, P1a]
        · linarith only [htop, P2b, P1a, P0a]
      · linarith only [h123_3, h013_1, htop, P1c, h012_0]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d02lo, htop, P2a, h013_0, d13hi, P1a]
        · linarith only [P1a, P2a, htop, d02lo, h013_1, h013_0, d23hi]
        · linarith only [P0a, P2a, htop, P1b]
        · linarith only [P1a, htop, d23hi, h012_0, h013_0, P2c, d12lo]
        · linarith only [P2c, htop, h123_3, P0a, h012_0]
        · linarith only [htop, P1c, P2c, h013_2]
      · linarith only [htop, d12lo, d23hi, P1c, h012_2, P0a]
    · linarith only [P0a, h012_2, h013_2, h123_1, htop]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h013_0, h023_1, h012_1]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, d23hi, h023_2, htop, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, htop, h013_1, h012_3, h123_4, P2a]
        · linarith only [d23hi, hn, P1a, P2a, h012_0, htop, d12lo]
        · linarith only [P0a, P2a, h013_2, h012_3, htop]
        · linarith only [h012_0, P2b, htop, d12lo, d23hi, P1a]
        · linarith only [P0a, htop, h012_3, P2c, h013_1]
        · linarith only [htop, d12lo, d23hi, h012_0, P2a, P1a]
      · linarith only [h012_3, P0a, P1a, h013_0, htop, h123_4]
      · linarith only [h013_2, htop, h123_4, P0a, P1a]
      · linarith only [P1c, h012_3, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1b, P0a, P2a, htop, h013_1, h123_4]
        · linarith only [P1a, htop, d12lo, h012_0, d23hi, P2a]
        · linarith only [P1b, P0a, P2a, htop, h013_1, h013_0]
        · linarith only [htop, h123_4, P2c]
        · linarith only [P1b, P0a, h013_1, htop, P2c]
        · linarith only [h013_2, P1c, P2c, htop]
      · linarith only [h013_0, P0a, h123_4, htop, P1c]
    · linarith only [h023_2, h012_0, P0a, htop]
  · linarith only [h023_1, h013_0, h123_0]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, P0a, d01hi, d12lo, h012_1, htop]
    · linarith only [P0a, d12lo, h123_2, h012_1, htop, d01hi]
    · linarith only [h023_2, h123_2, htop, P0a]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, d01hi, htop, P0a, d23lo]
    · linarith only [h123_2, P0a, htop, d02hi, d23lo]
    · linarith only [htop, h123_2, h012_0, P0a]
#print axioms lower_no_high_middle_middle_203

theorem lower_no_high_middle_middle_213 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : Middle n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h012_0, d23hi, htop, h123_2, d01lo]
    · linarith only [P0a, h012_2, d23hi, d01lo, htop]
    · linarith only [P0a, h123_2, h012_1, htop]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_0, h123_2, htop, P0a, d12hi, d01lo]
    · linarith only [h023_2, htop, h012_0, d01lo, d12hi, P0a]
    · linarith only [P0a, h023_2, h123_2, htop]
  · linarith only [h123_0, h023_2, h123_1, h012_1]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P0a, P1a, h012_3, htop, h123_4]
      · linarith only [d12hi, P1a, d23lo, P0a, h013_2, h012_3, htop]
      · linarith only [P0a, h012_1, h013_2, htop, P1a, h123_4]
      · linarith only [h012_3, P0a, d23lo, htop, d12hi, P1c]
      · linarith only [h012_1, h123_4, htop, P1c, P0a]
      · linarith only [P1c, h013_2, htop]
    · linarith only [d23lo, h023_2, htop, d12hi, P0a]
    · linarith only [h012_1, h023_2, htop, P0a]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h012_2, htop, h123_3]
      · linarith only [P1a, h123_3, htop, h013_2]
      · linarith only [P1a, h013_2, h012_2, htop]
      · linarith only [h123_3, htop, P1c]
      · linarith only [P1c, htop, h012_2]
      · linarith only [htop, h013_2, P1c]
    · linarith only [h012_0, h013_2, P0a, h123_0, d12hi, htop, d23lo]
    · linarith only [htop, h012_2, P0a, h013_2, h123_0]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h012_1, htop, d12lo, d13hi, h013_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h013_2, h123_3, htop]
      · linarith only [h012_2, htop, P1a, h123_3]
      · linarith only [h012_2, htop, P1a, h013_2]
      · linarith only [htop, h123_3, P1c]
      · linarith only [P1c, htop, h013_2]
      · linarith only [P1c, htop, h012_2]
    · linarith only [h012_2, htop, h013_2, P0a, h123_1]
  · linarith only [h012_2, h013_2, h123_1]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, P0a, d23hi, htop, d12lo]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [d23hi, htop, d12lo, P1a, h013_2, h012_3, P0a]
      · linarith only [h123_4, P1a, htop, P0a, h012_3]
      · linarith only [h123_4, h013_2, P1a, P0a, h012_0, htop]
      · linarith only [P0a, P1c, d12lo, htop, h012_3, d23hi]
      · linarith only [h013_2, htop, P1c]
      · linarith only [h012_0, h123_4, P1c, htop, P0a]
    · linarith only [h023_2, P0a, h012_0, htop]
  · linarith only [h023_1, h013_0, h123_0]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h023_2, d01hi, h012_1, d12lo, P0a]
    · linarith only [d01hi, d12lo, h123_2, htop, P0a, h012_1]
    · linarith only [h023_2, h123_2, P0a, htop]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, d23lo, P0a, h012_2, htop]
    · linarith only [d02hi, d23lo, h123_2, htop, P0a]
    · linarith only [h123_2, h012_0, P0a, htop]
#print axioms lower_no_high_middle_middle_213

theorem lower_no_high_middle_middle_301 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d03 d13 d23 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_4]
    · linarith only [htop, P0a, d01lo, h012_2, h123_0, d23hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_1, h123_2, htop, h013_3, P0a, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P0a, h013_3, P2a, h123_2]
        · linarith only [P2a, htop, h123_1, h012_2, h013_3, P0a]
        · linarith only [P2a, h013_1, P1a, h012_0, htop, hn]
        · linarith only [h123_1, h013_3, P2c, htop, P0a]
        · linarith only [h012_0, htop, P2b, h013_1, P1a]
        · linarith only [P2b, h013_1, P1a, htop, h012_0]
      · linarith only [h012_2, P1a, P0a, h123_2, htop]
      · linarith only [h013_3, htop, P1c]
      · linarith only [P1c, P0a, h123_2, h012_1, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h123_2, htop, P2a, P1b]
        · linarith only [P0a, htop, h123_1, P1b, h012_2, P2a]
        · linarith only [htop, P1a, h012_0, P2a, h013_1]
        · linarith only [h123_1, htop, P2c, P0a, P1b]
        · linarith only [P2c, htop, h013_1, P0a, h123_2]
        · linarith only [P2c, htop, h012_2]
  · have G0 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, P0a, h012_0, d12hi, h123_2, h023_0]
    · linarith only [htop, h012_0, d13hi, d01lo, P0a, h023_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [d12hi, h123_2, htop, h023_2, d01lo, P1a]
      · linarith only [h023_1, h012_4, P1a, htop, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [hn, htop, P1a, P0a, P2a]
        · linarith only [h023_2, h012_4, P2a, h123_0, htop]
        · linarith only [h023_2, htop, h123_2, h012_0, P2a]
        · linarith only [P1a, htop, P2a, P0a]
        · linarith only [htop, P1a, P0a, P2a]
        · linarith only [P2c, h012_0, htop, h123_0, h023_2]
      · linarith only [d12hi, h123_2, d01lo, h023_1, P1c, htop]
      · linarith only [htop, P1c, h123_0, P0a, h023_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1b, htop, P0a, P2a]
        · linarith only [h123_0, h012_0, htop, P2a, P1a, h023_1, d12hi, d01lo]
        · linarith only [h023_1, h012_0, P1a, P2a, htop, h123_2]
        · linarith only [h012_4, P2c, htop, P1c]
        · linarith only [htop, h023_1, h123_2, P2c, P0a]
        · linarith only [htop, h012_0, P1a, P2c, h123_0, h023_1]
  · linarith only [h123_0, h012_1, h023_2, h123_1]
  · have G0 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h023_4]
    · linarith only [htop, P0a, h013_4]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_1, P0a, P1a, h023_2, h012_3, htop]
      · linarith only [htop, h023_0, P0a, P1a, h013_2, h012_3]
      · linarith only [P1a, P0a, h013_2, h023_2, htop]
      · linarith only [P1c, htop, h012_3]
      · linarith only [P1c, h013_1, htop, h023_2, P0a]
      · linarith only [htop, h013_2, P1c, h023_0, P0a]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h123_0, h013_2, h012_2]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, d23lo, h013_2, P0a, htop]
    · linarith only [d23lo, h123_0, h012_2, P0a, h013_1, htop, d12hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_3, h013_0, P1a, htop, h012_2]
      · linarith only [h012_1, P1a, h013_2, htop, h123_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_3, h012_2, htop, P2a]
        · linarith only [P2a, h013_2, h123_3, htop]
        · linarith only [P2a, h012_2, h013_2, htop]
        · linarith only [h123_0, P0a, P2a, P1a, htop, h012_0]
        · linarith only [htop, P2a, P0a, h012_0, P1a, h123_0]
        · linarith only [h013_2, P2c, htop]
      · linarith only [P1c, h013_0, htop, h012_1, h123_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h123_3, h012_2, P2a]
        · linarith only [d23lo, d12hi, htop, P2a, h123_0, P1a, h013_0]
        · linarith only [htop, P1a, P2a, h013_0, h012_2]
        · linarith only [h123_3, P2c, htop]
        · linarith only [htop, h012_2, P2c]
        · linarith only [htop, P1a, P2c, h013_0]
      · linarith only [h013_2, P0a, h123_0, P1c, htop]
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, htop, h012_2, h013_0, d12lo, P0a]
    · linarith only [h013_2, h012_2, d12lo, P0a, htop, d23hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_0, h123_3, htop, P1a, h013_2]
      · linarith only [h123_3, P1a, htop, h013_1, h012_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_2, htop, h123_3, P2a]
        · linarith only [P2a, htop, h012_1, P1a, hn, h123_1, P0a]
        · linarith only [htop, h012_2, h013_2, P2a]
        · linarith only [P0a, h012_1, htop, h123_1, P2b, P1a]
        · linarith only [h013_2, P2c, htop]
        · linarith only [P1a, h123_1, P2a, P0a, htop, h012_1]
      · linarith only [h123_3, h013_1, htop, h012_0, P1c]
      · linarith only [P0a, P1c, h013_2, htop, h123_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, P2a, htop, h123_3, h013_1]
        · linarith only [h012_2, P2a, htop, h123_3]
        · linarith only [P1a, h012_2, htop, P2a, h013_1]
        · linarith only [htop, h123_3, P2c]
        · linarith only [htop, h013_1, P1a, P2c]
        · linarith only [P2c, h012_2, htop]
  · linarith only [h012_2, h123_1, h013_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h013_0, h012_1, h023_1]
  · have G0 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_4, P0a, htop]
    · linarith only [h023_4, htop, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_3, h023_1, P0a, P1a, h013_2, htop]
      · linarith only [htop, h012_3, P0a, h023_2, P1a, h013_0]
      · linarith only [P1a, htop, h013_2, P0a, h023_2]
      · linarith only [h012_3, P1c, htop]
      · linarith only [h013_2, P0a, htop, h023_1, P1c]
      · linarith only [htop, h013_0, P0a, P1c, h023_2]
  · linarith only [h013_0, h023_1, h123_0]
  · have G0 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, P0a, h023_2, htop, d01hi, d13lo]
    · linarith only [htop, P0a, h123_2, d03hi, d12lo]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h012_4, P1a, h123_2, h023_0]
      · linarith only [P1a, d12lo, htop, h023_2, h123_2, d01hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, h123_1, htop, h012_4, P2a]
        · linarith only [htop, P2a, P1a, P0a, hn]
        · linarith only [h012_1, h123_2, h023_2, htop, P2a]
        · linarith only [P0a, P2b, P1a, htop]
        · linarith only [htop, h023_2, P2c, h123_1, h012_1]
        · linarith only [P1a, P2a, htop, P0a]
      · linarith only [htop, P1c, d01hi, h123_2, d12lo, h023_0]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_1, h023_0, h012_1, P1a, d12lo, htop, d01hi]
        · linarith only [P1b, htop, P2a, P0a]
        · linarith only [h012_1, P2a, htop, P1a, h123_2, h023_0]
        · linarith only [P1c, h012_4, htop, P2c]
        · linarith only [h023_0, h123_1, h012_1, P2c, P1a, htop]
        · linarith only [P0a, h123_2, P2c, h023_0, htop]
      · linarith only [htop, h123_1, P0a, h023_2, P1c]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, d23lo, h013_2, d01hi]
    · linarith only [P0a, htop, h013_4]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h012_2, htop, h013_3, P2a, h123_0]
        · linarith only [P0a, htop, P2a, h123_2, h013_3]
        · linarith only [h013_0, P1a, htop, P2a, hn, h012_1]
        · linarith only [h013_3, htop, h123_0, P2c, P0a]
        · linarith only [P2b, h013_0, P1a, htop, h012_1]
        · linarith only [h012_1, h013_0, P2b, P1a, htop]
      · linarith only [h012_0, P1a, h013_3, P0a, htop, h123_2]
      · linarith only [P1a, h123_2, P0a, h012_2, htop]
      · linarith only [h013_3, htop, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_2, htop, P0a, P2a, P1b, h123_0]
        · linarith only [P2a, htop, P1b, P0a, h123_2]
        · linarith only [h012_1, P2a, P1a, htop, h013_0]
        · linarith only [htop, P1b, P2c, h123_0, P0a]
        · linarith only [htop, P2c, h012_2]
        · linarith only [P2c, P0a, h013_0, htop, h123_2]
      · linarith only [P0a, htop, P1c, h012_0, h123_2]
#print axioms lower_no_high_middle_middle_301

theorem lower_no_high_middle_middle_302 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d03 d13 d23 t))
    (P1 : Middle n (sortedGaps d01 d02 d03 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_4, P0a]
    · linarith only [P0a, htop, d23hi, d01lo, h012_2, h123_0]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_3, h012_1, htop, h123_2, P1a, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_2, P0a, htop, h013_3, h012_0]
        · linarith only [P2a, P0a, h013_3, htop, h012_2]
        · linarith only [htop, h013_1, h123_1, P1a, hn, P2a]
        · linarith only [h013_3, h012_0, P2c, P0a, htop]
        · linarith only [P1a, htop, h023_1, P2b]
        · linarith only [P1a, h023_1, P2b, htop]
      · linarith only [h012_2, htop, h123_2, P0a, P1a]
      · linarith only [P1c, htop, h013_3]
      · linarith only [htop, P1c, h012_1, P0a, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, P2a, htop, h123_2, P1b, h012_0]
        · linarith only [P0a, P2a, h012_2, P1b, htop]
        · linarith only [P1a, htop, h123_1, h013_1, P2a]
        · linarith only [h012_0, P2c, P0a, htop, P1b]
        · linarith only [P2c, htop, h123_2]
        · linarith only [P2c, h012_2, P1c, htop]
  · have G0 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h123_2, d01lo, h023_0, h012_0, d12hi]
    · linarith only [h012_0, P0a, d01lo, d13hi, htop, h023_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, d01lo, h023_2, d12hi, P1a, h123_2]
      · linarith only [h012_4, htop, P1a, h023_1, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_2, htop, h012_4]
        · linarith only [h023_2, P2a, htop, h012_4]
        · linarith only [htop, h123_2, P2a, h023_2]
        · linarith only [htop, h012_0, P0a, h123_0, P2a, P1a]
        · linarith only [P1a, htop, h123_0, P0a, h012_0, P2a]
        · linarith only [htop, h023_2, P2c]
      · linarith only [d12hi, htop, h123_2, P1c, h023_1, d01lo]
      · linarith only [P0a, htop, P1c, h023_2, h123_0]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, P2a, h123_2, htop]
        · linarith only [htop, d01lo, d12hi, P1a, P2a, h023_1, h012_0]
        · linarith only [htop, P2a, P1a, h123_2, h023_1]
        · linarith only [P2c, htop, h012_4]
        · linarith only [h123_2, htop, P2c]
        · linarith only [h023_1, P2c, htop, P1a]
  · linarith only [h123_1, h012_1, h023_2, h123_0]
  · have G0 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h023_4, htop]
    · linarith only [htop, h013_4, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h013_1, htop, P0a, h012_3, h023_2]
      · linarith only [P1a, h023_0, htop, P0a, h013_2, h012_3]
      · linarith only [P1a, h023_2, htop, P0a, h013_2]
      · linarith only [P1c, h012_3, htop]
      · linarith only [h023_2, h013_1, htop, P0a, P1c]
      · linarith only [h023_0, P1c, h013_2, htop, P0a]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, d23lo, htop, P0a, h013_2]
    · linarith only [d23lo, P0a, h013_1, d12hi, htop, h123_0, h012_2]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h013_0, h012_2, h123_3, htop, P1a]
      · linarith only [h013_2, P1a, h123_3, htop, h012_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1a, hn, P0a, P2a, htop]
        · linarith only [h013_2, h012_0, h123_3, htop, P2a]
        · linarith only [h123_0, P2a, h013_2, htop, h012_2]
        · linarith only [P2a, P1a, htop, P0a]
        · linarith only [P0a, P2a, P1a, htop]
        · linarith only [h013_2, P2c, h123_0, htop, h012_0]
      · linarith only [h123_3, h013_0, h012_1, htop, P1c]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P1b, htop, P0a, P2a]
        · linarith only [P1a, htop, h123_0, P2a, h013_0, d12hi, h012_0, d23lo]
        · linarith only [P1a, P2a, htop, h013_0, h012_2, h123_0]
        · linarith only [htop, h013_0, P2c, P0a, h123_3]
        · linarith only [htop, P2c, h012_2, P1c]
        · linarith only [P2c, h012_0, P1a, h013_0, h123_0, htop]
      · linarith only [h013_2, P0a, P1c, h123_0, htop]
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d13hi, h013_0, d12lo, P0a, h012_2]
    · linarith only [P0a, d23hi, htop, h013_2, h012_2, d12lo]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h013_2, h123_3, h012_0, htop]
      · linarith only [htop, h012_2, P1a, h013_1, h123_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_2, htop, h123_3, P2a, h012_1]
        · linarith only [P1a, hn, P2a, P0a, htop]
        · linarith only [h013_2, h123_1, h012_2, P2a, htop]
        · linarith only [P2b, P0a, htop, P1a]
        · linarith only [h123_1, h013_2, htop, h012_1, P2c]
        · linarith only [htop, P0a, P2a, P1a]
      · linarith only [h013_1, h123_3, h012_0, htop, P1c]
      · linarith only [h013_2, P0a, h123_1, P1c, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d12lo, P1a, h013_1, P2a, d23hi, h123_1, htop, h012_1]
        · linarith only [P2a, P1b, P0a, htop]
        · linarith only [P2a, h012_2, h013_1, P1a, h123_1, htop]
        · linarith only [P2c, h013_1, htop, P0a, h123_3]
        · linarith only [htop, h012_1, h013_1, P2c, h123_1, P1a]
        · linarith only [htop, P2c, P1c, h012_2]
  · linarith only [h013_2, h012_2, h123_1]
  · linarith only [h012_1, h023_1, h013_0]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h013_4]
    · linarith only [h023_4, htop, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h012_3, h013_2, P1a, P0a, h023_1, htop]
      · linarith only [h012_3, P0a, h023_2, P1a, htop, h013_0]
      · linarith only [h013_2, h023_2, P1a, htop, P0a]
      · linarith only [htop, h012_3, P1c]
      · linarith only [htop, h023_1, h013_2, P0a, P1c]
      · linarith only [h023_2, h013_0, P1c, P0a, htop]
  · linarith only [h023_1, h013_0, h123_0]
  · have G0 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, htop, P0a, h012_1, h023_2, d13lo]
    · linarith only [d12lo, P0a, d03hi, h123_2, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, h023_0, h123_2, htop, h012_4]
      · linarith only [h123_2, d01hi, P1a, h023_2, d12lo, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h023_2, P2a, h012_4]
        · linarith only [htop, h123_2, P2a, h012_4]
        · linarith only [P2a, h023_2, h123_2, htop]
        · linarith only [h012_1, P0a, P1a, htop, P2b, h123_1]
        · linarith only [htop, h023_2, P2c]
        · linarith only [htop, h123_1, P2a, h012_1, P0a, P1a]
      · linarith only [h123_2, P1c, htop, d12lo, h023_0, d01hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [d12lo, P1a, P2a, h012_1, h023_0, htop, d01hi]
        · linarith only [htop, P2a, h123_2, h012_4]
        · linarith only [h023_0, P1a, P2a, h123_2, htop]
        · linarith only [P2c, h012_4, htop]
        · linarith only [P2c, h023_0, htop, P1a]
        · linarith only [h123_2, P2c, htop]
      · linarith only [P1c, h023_2, P0a, h123_1, htop]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, h013_2, d01hi, d23lo]
    · linarith only [h013_4, P0a, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h012_2, P2a, h013_3, P0a]
        · linarith only [htop, P0a, P2a, h123_2, h013_3, h012_1]
        · linarith only [htop, h013_0, P1a, h123_0, P2a, hn]
        · linarith only [h013_3, h012_1, P0a, P2c, htop]
        · linarith only [h123_0, h013_0, P1a, P2b, htop]
        · linarith only [P2b, P1a, h023_0, htop]
      · linarith only [h013_3, h012_0, h123_2, P0a, P1a, htop]
      · linarith only [P1a, h012_2, P0a, h123_2, htop]
      · linarith only [h013_3, P1c, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, P1b, h012_2, htop, P2a]
        · linarith only [htop, h012_1, P2a, P0a, h123_2, P1b]
        · linarith only [h123_0, P2a, h013_0, htop, P1a]
        · linarith only [P1b, P2c, h012_1, htop, P0a]
        · linarith only [P2c, htop, h012_2, P1c]
        · linarith only [htop, P2c, h123_2]
      · linarith only [h123_2, P0a, P1c, h012_0, htop]
#print axioms lower_no_high_middle_middle_302

theorem lower_no_high_middle_middle_312 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1/2)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d03 d13 d23 t))
    (P1 : Middle n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_4]
    · linarith only [h123_0, P0a, d23hi, h012_2, d01lo, htop]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, htop, P0a, h123_2, h013_3]
      · linarith only [h012_2, htop, h123_1, P0a, h013_3, P1a]
      · linarith only [htop, h123_2, P1a, P0a, h013_1, h012_2]
      · linarith only [h123_1, P0a, htop, P1c, h013_3]
      · linarith only [htop, P0a, h123_2, h013_1, P1c]
      · linarith only [h012_2, htop, P1c]
  · have G0 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, h023_0, d12hi, P0a, h123_2, htop, h012_0]
    · linarith only [d13hi, h023_2, htop, P0a, d01lo, h012_0]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, htop, h123_2, P2a]
        · linarith only [h012_4, htop, h023_2, P2a]
        · linarith only [h123_2, htop, h023_2, P2a]
        · linarith only [d12hi, d01lo, P0a, h023_1, htop, P2b, P1a]
        · linarith only [h123_2, htop, P2c]
        · linarith only [d12hi, h023_1, P0a, htop, d01lo, P2a, P1a]
      · linarith only [htop, h012_4, h123_0, h023_2, P1a]
      · linarith only [h012_0, htop, h023_2, h123_2, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h012_4, P1b, htop, h123_0]
        · linarith only [P0a, P1a, htop, d12hi, h023_1, P2a, d01lo]
        · linarith only [P2a, h013_1, P1b, htop, h023_0]
        · linarith only [P2c, htop, h012_4]
        · linarith only [P1b, P2c, h123_0, htop]
        · linarith only [h023_2, P2c, htop]
      · linarith only [h123_2, P1c, h023_1, P0a, htop]
      · linarith only [P1c, htop, h123_0, h023_2, h012_0]
  · linarith only [h023_2, h012_1, h123_0, h123_1]
  · have G0 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_4, P0a, htop]
    · linarith only [htop, h013_4, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h023_2, P1a, P0a, htop, h012_3]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_3, P0a, P2a, htop, h013_2]
        · linarith only [d12hi, h023_2, P2a, h013_2, P0a, d01lo, htop]
        · linarith only [P1a, h012_3, htop, P2a, h023_2, h013_2]
        · linarith only [d01lo, d12hi, P2c, h013_2, htop, P0a]
        · linarith only [h023_0, P2b, P1a, htop, h013_1]
        · linarith only [h013_1, P2b, h023_0, htop, P1a]
      · linarith only [h013_2, htop, P1a, h023_2, h012_1, P0a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P1a, d01lo, P2a, d02hi, P0a]
        · linarith only [P1a, d12hi, htop, P2a, d01lo, h023_2, P0a]
        · linarith only [h013_1, P1b, htop, h023_0, P2a]
        · linarith only [htop, P1a, d12hi, P0a, P2c, d01lo]
        · linarith only [h012_3, P1c, P2c, htop]
        · linarith only [h023_2, htop, P2c]
      · linarith only [h012_1, htop, h023_2, P1c, P0a]
      · linarith only [h013_2, P1c, htop]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h012_2, h123_0, h013_2]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, htop, h013_2, d01hi, P0a]
    · linarith only [h013_1, htop, h012_2, h123_0, P0a, d23lo, d12hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_3, P1a, htop, h012_2]
      · linarith only [h123_3, htop, h013_2, P1a]
      · linarith only [h013_2, P1a, h012_2, htop]
      · linarith only [P1c, htop, h123_3]
      · linarith only [P1c, htop, h012_2]
      · linarith only [P1c, htop, h013_2]
  · have G0 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, h013_0, P0a, htop, h012_2, d13hi]
    · linarith only [h013_2, h012_2, htop, P0a, d12lo, d23hi]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [h123_3, h013_2, P1a, htop]
      · linarith only [h123_3, h012_2, htop, P1a]
      · linarith only [h013_2, h012_2, htop, P1a]
      · linarith only [h123_3, htop, P1c]
      · linarith only [htop, P1c, h013_2]
      · linarith only [h012_2, htop, P1c]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h012_1, h023_1, h013_0]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_4, htop]
    · linarith only [htop, h023_4, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, h013_2, d12lo, P2a, h023_2, d01hi, htop]
        · linarith only [h013_2, htop, P2a, P0a, h012_3]
        · linarith only [h023_1, htop, h013_0, hn, P2a, P1a]
        · linarith only [P2c, P0a, d01hi, h013_2, d12lo, htop]
        · linarith only [htop, h013_0, P2b, P1a, h023_1]
        · linarith only [P2b, P1a, htop, h013_0, h023_1]
      · linarith only [htop, P0a, h012_3, P1a, h023_2]
      · linarith only [P0a, h012_0, h023_2, h013_2, P1a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, P1b, P2a, d01hi, htop, d12lo, P0a]
        · linarith only [htop, P2a, h012_3, P1b, P0a]
        · linarith only [h023_1, h013_0, htop, P1a, P2a]
        · linarith only [d01hi, htop, P2c, d12lo, P1b, P0a]
        · linarith only [P2c, h023_2, htop]
        · linarith only [htop, P2c, h012_3, P1c]
      · linarith only [htop, P1c, h013_2]
      · linarith only [P1c, h023_2, P0a, h012_0, htop]
  · linarith only [h023_1, h123_0, h013_0]
  · have G0 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, d13lo, d01hi, htop, P0a, h012_1]
    · linarith only [d03hi, d12lo, h123_2, htop, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [htop, h123_1, h023_2, P1a, h012_4]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, P2a, htop, h023_2]
        · linarith only [h123_2, htop, P2a, h012_4]
        · linarith only [h023_2, htop, h123_2, P2a]
        · linarith only [d12lo, h023_0, d01hi, P2a, P1a, P0a, htop]
        · linarith only [d12lo, P0a, d01hi, P2a, htop, h023_0, P1a]
        · linarith only [h123_2, P2c, htop]
      · linarith only [h023_2, P1a, htop, h012_1, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, P2a, htop, h023_2]
        · linarith only [P2a, htop, h123_1, d02hi, P1a, d12lo]
        · linarith only [h023_2, htop, P1a, h123_1, P2a]
        · linarith only [htop, P2c, h012_4]
        · linarith only [P2c, h023_2, htop]
        · linarith only [h123_1, P1a, htop, P2c]
      · linarith only [P1c, h023_2, h123_1, h012_1, htop]
      · linarith only [htop, h023_0, P1c, P0a, h123_2]
  · have G0 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [Middle] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_2, P0a, d01hi, d23lo, htop]
    · linarith only [htop, h013_4, P0a]
    · rcases P1 with P1a | P1a | P1a | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩ | ⟨P1a, P1b, P1c⟩
      · linarith only [P1a, htop, P0a, h123_0, h013_3, h012_2]
      · linarith only [P1a, htop, h013_3, P0a, h123_2]
      · linarith only [h012_2, htop, P1a, h013_0, h123_2, P0a]
      · linarith only [P0a, P1c, h013_3, htop, h123_0]
      · linarith only [htop, h012_2, P1c]
      · linarith only [P0a, h123_2, h013_0, htop, P1c]
#print axioms lower_no_high_middle_middle_312

theorem upper_no_high_high_middle_012 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, h123_2, htop, d23hi, h012_1, P0a]
    · linarith only [P0a, h012_0, h013_3, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d23hi, P1a, htop, d01lo, h123_2]
      · linarith only [d13hi, d01lo, htop, P1a, h012_2]
      · linarith only [h012_2, htop, P1a, h123_0]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, h123_2, h023_2, P0a, htop, d12hi]
    · linarith only [P0a, htop, h013_3, h012_0]
    · rcases P1 with P1a | P1a | P1a
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h123_2, h012_4, htop]
        · linarith only [h023_2, htop, P2a, h012_4]
        · linarith only [htop, P0a, h123_1, P2a, h023_0, P1a, hn]
        · linarith only [htop, P2c, h012_4]
        · linarith only [P0a, P2b, htop, h023_0, h123_1, P1a]
        · linarith only [P1a, h123_1, htop, P0a, h023_0, P2b]
      · linarith only [h012_0, d12hi, h023_2, d01lo, P1a, h123_0, htop]
      · linarith only [h012_0, P1a, h023_2, htop, h123_2]
  · linarith only [h012_1, h123_0, h123_1, h023_2]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_3, P0a]
    · linarith only [htop, P0a, h013_0, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P0a, h123_4, h023_2, htop, P1a]
      · linarith only [h023_2, d12hi, P1a, htop, h013_2, P0a, d23lo]
      · linarith only [h013_2, htop, P1a, h123_1]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_0, d12hi, d23lo, h123_0, P0a, h012_2]
    · linarith only [h123_0, h013_2, P0a, htop, d23lo, d02hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_0, htop, h012_2, d12hi, d23lo, P1a]
      · linarith only [d23lo, htop, P1a, h123_0, d12hi, h013_2]
      · linarith only [P1a, h012_2, h013_2, htop]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_2, htop, P0a, d13hi, h012_0, d12lo]
    · linarith only [d03hi, d12lo, h012_2, P0a, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, P1a, h013_2, d13hi, htop]
      · linarith only [h012_2, P1a, htop, d12lo, d13hi]
      · linarith only [htop, h012_2, h013_2, P1a]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_1, h012_3, htop, P0a]
    · linarith only [P0a, h012_3, h023_0, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, P1a, h013_2, d12lo]
      · linarith only [P0a, P1a, h123_4, htop, h023_2]
      · linarith only [h013_2, h123_0, htop, P1a]
  · linarith only [h123_0, h013_0, h023_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h123_2, h023_0, htop, d12lo, d01hi, h012_1]
    · linarith only [P0a, h023_2, d01hi, h123_2, d12lo, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h012_1, P1a, htop, d12lo, h123_1, d01hi, h023_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h012_4, h023_2, P2a]
        · linarith only [h123_2, P2a, h012_4, htop]
        · linarith only [P2a, P1a, h023_1, h123_0, P0a, htop, hn]
        · linarith only [h012_4, htop, P2c]
        · linarith only [h023_1, P0a, htop, P2b, P1a, h123_0]
        · linarith only [P2b, P1a, P0a, h023_1, htop, h123_0]
      · linarith only [htop, P1a, h012_1, h023_2, h123_2]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, h012_1, htop, P0a]
    · linarith only [d01hi, h012_0, htop, h123_2, d23lo, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d23lo, htop, P1a, d01hi, h012_2, h123_0]
      · linarith only [d01hi, P1a, d23lo, h123_2, htop]
      · linarith only [P1a, htop, h013_2]
#print axioms upper_no_high_high_middle_012

theorem upper_no_high_high_middle_013 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d01 d12 d13 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, h123_2, d01lo, htop, h012_1, P0a]
    · linarith only [htop, h013_3, h012_0, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d23hi, d01lo, P1a, h123_2]
      · linarith only [htop, h012_2, d01lo, P1a, d13hi]
      · linarith only [P1a, h012_2, htop, h123_0]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, h023_2, h123_2, d12hi, P0a]
    · linarith only [htop, P0a, h013_3, h012_0]
    · rcases P1 with P1a | P1a | P1a
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, h023_0, htop, h123_2, h012_4]
        · linarith only [h023_2, htop, P2a, h012_4, h123_1]
        · linarith only [P2a, P1a, htop, P0a, hn]
        · linarith only [h123_1, h012_4, P2c, h023_0, htop]
        · linarith only [P2b, P1a, P0a, htop]
        · linarith only [P1a, P0a, htop, P2b]
      · linarith only [d12hi, h023_2, htop, h123_0, h012_0, d01lo, P1a]
      · linarith only [htop, h123_2, h012_0, h023_2, P1a]
  · linarith only [h123_0, h023_2, h123_1, h012_1]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop]
    · linarith only [h013_0, P0a, htop, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_2, h123_4, P0a, htop, P1a]
      · linarith only [d12hi, P1a, P0a, h013_2, h023_2, d23lo, htop]
      · linarith only [h013_2, P1a, htop, h123_1]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h123_0, h013_2, h012_2]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_0, h012_2, h013_0, d12hi, d23lo, P0a, htop]
    · linarith only [htop, d02hi, h123_0, d23lo, h013_2, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_0, d23lo, P1a, htop, h012_2, d12hi]
      · linarith only [d12hi, htop, P1a, d23lo, h013_2, h123_0]
      · linarith only [h013_2, P1a, htop, h012_2]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_2, h012_0, d12lo, P0a, htop, d13hi]
    · linarith only [htop, P0a, d12lo, h012_2, d03hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, htop, h013_2, d13hi, P1a]
      · linarith only [d13hi, P1a, h012_2, d12lo, htop]
      · linarith only [h013_2, h012_2, htop, P1a]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_1, P0a, h012_3]
    · linarith only [h012_3, P0a, htop, h023_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, d01hi, h013_2, htop, P1a]
      · linarith only [P1a, h023_2, htop, P0a, h123_4]
      · linarith only [P1a, h013_2, h123_0, htop]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, P0a, d01hi, htop, d12lo, h012_1, h023_0]
    · linarith only [htop, P0a, h023_2, d01hi, d12lo, h123_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h012_1, P1a, htop, h123_1, d12lo, d01hi, h023_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_4, h023_2, h123_0, htop, P2a]
        · linarith only [h123_2, h012_4, P2a, htop, h023_1]
        · linarith only [P2a, P0a, hn, htop, P1a]
        · linarith only [h023_1, htop, P2c, h012_4, h123_0]
        · linarith only [htop, P2b, P1a, P0a]
        · linarith only [P1a, htop, P0a, P2b]
      · linarith only [P1a, h123_2, h023_2, htop, h012_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, h013_3, htop, P0a]
    · linarith only [P0a, d01hi, h012_0, d23lo, h123_2, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h012_2, d23lo, d01hi, h123_0, P1a]
      · linarith only [h123_2, d01hi, P1a, d23lo, htop]
      · linarith only [htop, P1a, h013_2]
#print axioms upper_no_high_high_middle_013

theorem upper_no_high_high_middle_021 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, P0a, d23hi, h123_2, htop, h012_1]
    · linarith only [P0a, h013_3, h012_0, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h123_2, d23hi, h012_0, d01lo]
      · linarith only [d01lo, h012_2, d23hi, htop, P1a]
      · linarith only [h123_2, htop, h012_1, P1a]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, h023_2, htop, P0a, d12hi, d01lo]
    · linarith only [htop, h012_0, h013_3, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01lo, h123_2, htop, d12hi, h012_0, P1a]
      · linarith only [P1a, h023_2, d12hi, d01lo, htop, h012_0]
      · linarith only [P1a, htop, h023_2, h123_2]
  · linarith only [h012_1, h123_1, h123_0, h023_2]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop]
    · linarith only [htop, P0a, h012_3, h013_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, P0a, htop, h013_2, h123_4]
      · linarith only [d12hi, h023_2, P1a, htop, d23lo]
      · linarith only [htop, h123_1, P0a, h023_2, h013_2, P1a]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h013_2, h012_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_0, d23lo, h123_0, htop, d12hi, P0a, h012_2]
    · linarith only [d02hi, h123_0, d23lo, h013_2, htop, P0a]
    · rcases P1 with P1a | P1a | P1a
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_2, htop, P2a, h123_3]
        · linarith only [P1a, P2a, htop, d12hi, d23lo, h013_1, hn, P0a]
        · linarith only [P2a, htop, h012_2, h013_2]
        · linarith only [d12hi, P2b, d23lo, htop, P0a, h013_1, P1a]
        · linarith only [h012_2, htop, P2c]
        · linarith only [P1a, h013_1, d12hi, P2a, P0a, htop, d23lo]
      · linarith only [d12hi, d23lo, h013_2, h012_0, htop, h123_0, P1a]
      · linarith only [htop, P1a, h123_0, h012_2, h013_2]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, d12lo, h012_0, P0a, htop, h013_2]
    · linarith only [d12lo, d03hi, P0a, h012_2, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h013_2, d12lo, h012_1, d13hi, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, P2a, htop, d23hi, hn, P1a, h013_0, d12lo]
        · linarith only [P2a, h123_3, h012_2, htop]
        · linarith only [h012_2, htop, h013_2, P2a]
        · linarith only [P2a, P1a, P0a, d12lo, h013_0, htop, d23hi]
        · linarith only [d12lo, P2a, htop, h013_0, d23hi, P1a, P0a]
        · linarith only [htop, P2c, h012_2]
      · linarith only [h013_2, h123_1, P1a, h012_2, htop]
  · linarith only [h123_1, h013_2, h012_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h012_1, h013_0, h023_1]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_3, P0a, htop, h013_1]
    · linarith only [P0a, htop, h023_0, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d23hi, P1a, h023_2, htop, d12lo]
      · linarith only [htop, h013_2, P0a, P1a, h123_4]
      · linarith only [h023_2, htop, P1a, h013_2, P0a, h123_0]
  · linarith only [h123_0, h013_0, h023_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, h012_1, htop, h123_2, h023_0, d12lo, P0a]
    · linarith only [h023_2, P0a, htop, h123_2, d12lo, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01hi, h012_1, P1a, h023_2, d12lo, htop]
      · linarith only [htop, h123_2, P1a, h012_1, d01hi, d12lo]
      · linarith only [htop, P1a, h023_2, h123_2]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h012_1, htop, h013_3]
    · linarith only [P0a, h012_0, htop, h123_2, d23lo, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, d23lo, htop, d01hi, h012_2]
      · linarith only [h123_2, d02hi, htop, d23lo, P1a]
      · linarith only [h012_2, h123_2, h023_1, P0a, P1a, htop]
#print axioms upper_no_high_high_middle_021

theorem upper_no_high_high_middle_023 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, d01lo, h123_2, P0a, h012_1, htop]
    · linarith only [h012_0, h013_3, P0a, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01lo, h123_2, h012_0, htop, P1a, d23hi]
      · linarith only [htop, P1a, d01lo, h012_2, d23hi]
      · linarith only [htop, P1a, h123_2, h012_1]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12hi, h023_2, P0a, h123_2, htop, d01lo]
    · linarith only [P0a, htop, h013_3, h012_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_2, P1a, h012_0, d12hi, htop, d01lo]
      · linarith only [h012_0, htop, P1a, d12hi, d01lo, h023_2]
      · linarith only [htop, h023_2, P1a, h123_2]
  · linarith only [h123_1, h023_2, h012_1, h123_0]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, P0a, htop]
    · linarith only [h013_0, P0a, htop, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, P0a, h123_4, htop, P1a]
      · linarith only [htop, P1a, d23lo, d12hi, h023_2]
      · linarith only [h023_2, P1a, P0a, h123_1, h013_2, htop]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h012_2, h123_0, h013_2]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d23lo, d12hi, h123_0, h013_0, htop, h012_2]
    · linarith only [h123_0, P0a, h013_2, d23lo, htop, d02hi]
    · rcases P1 with P1a | P1a | P1a
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h012_2, P2a, htop, h013_2, d23lo, d12hi]
        · linarith only [h012_2, htop, P2a, h123_3, h013_1]
        · linarith only [P0a, P1a, P2a, htop, hn]
        · linarith only [h013_1, d23lo, h012_2, P2c, d12hi, htop]
        · linarith only [P2b, P1a, htop, P0a]
        · linarith only [P0a, htop, P1a, P2b]
      · linarith only [h123_0, htop, d23lo, d12hi, h012_0, h013_2, P1a]
      · linarith only [h013_2, h012_2, h123_0, htop, P1a]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_0, h013_2, d12lo, d13hi, P0a, htop]
    · linarith only [P0a, d12lo, h012_2, htop, d03hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, htop, h012_1, P1a, d13hi, d12lo]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_0, h123_3, h012_2, P2a, htop]
        · linarith only [h013_2, d23hi, d12lo, h012_2, P2a, htop]
        · linarith only [P0a, P2a, hn, htop, P1a]
        · linarith only [d23hi, htop, P2c, d12lo, h012_2, h013_0]
        · linarith only [P0a, P2b, htop, P1a]
        · linarith only [htop, P0a, P2b, P1a]
      · linarith only [h012_2, P1a, h123_1, htop, h013_2]
  · linarith only [h013_2, h012_2, h123_1]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_3, htop, P0a, h013_1]
    · linarith only [P0a, h012_3, htop, h023_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, htop, P1a, d23hi, h023_2]
      · linarith only [h123_4, h013_2, P1a, htop, P0a]
      · linarith only [h123_0, h023_2, htop, P1a, P0a, h013_2]
  · linarith only [h023_1, h123_0, h013_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d12lo, h012_1, d01hi, P0a, h123_2, h023_0]
    · linarith only [d12lo, htop, h123_2, h023_2, P0a, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, P1a, d12lo, h012_1, h023_2]
      · linarith only [h012_1, h123_2, d01hi, d12lo, P1a, htop]
      · linarith only [htop, h123_2, h023_2, P1a]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h013_3, htop, P0a, h012_1]
    · linarith only [h012_0, htop, h123_2, d01hi, P0a, d23lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, h012_2, P1a, d23lo]
      · linarith only [d02hi, htop, P1a, h123_2, d23lo]
      · linarith only [htop, h012_2, h023_1, P0a, P1a, h123_2]
#print axioms upper_no_high_high_middle_023

theorem upper_no_high_high_middle_031 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h012_1, h123_2, d23hi, d01lo]
    · linarith only [P0a, htop, h012_0, h013_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_4, htop, P1a]
      · linarith only [htop, h012_2, d23hi, h123_0, d01lo, P1a]
      · linarith only [h123_2, h012_2, htop, P0a, P1a]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12hi, htop, h123_2, P0a, d01lo, h023_2]
    · linarith only [htop, h012_0, h013_3, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h012_0, h123_2, h023_0, d01lo, d12hi, P1a]
      · linarith only [d01lo, P1a, htop, d13hi, h023_2, h012_0]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [hn, P2a, P1a, P0a, htop]
        · linarith only [P2a, h123_0, h012_4, htop, h023_2]
        · linarith only [h012_0, P2a, h023_2, htop, h123_2]
        · linarith only [P2a, P0a, P1a, htop]
        · linarith only [P0a, P1a, P2a, htop]
        · linarith only [htop, P2c, h012_0, h023_2, h123_0]
  · linarith only [h123_1, h123_0, h023_2, h012_1]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h013_3]
    · linarith only [h013_0, htop, P0a, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h023_4]
      · linarith only [P1a, htop, h013_4]
      · linarith only [htop, P0a, P1a, h023_2, h013_2]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h013_2, h012_2, h123_0]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, P0a, h013_0, htop, d12hi, h123_0, d23lo]
    · linarith only [P0a, h013_2, d02hi, htop, d23lo, h123_0]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d01hi, h013_2, d23lo, P1a]
      · linarith only [P1a, d12hi, htop, h012_2, d23lo, h123_0, h013_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [hn, P2a, h123_0, h012_0, P1a, P0a, htop]
        · linarith only [h013_2, h123_3, P2a, htop]
        · linarith only [h012_2, h013_2, P2a, htop]
        · linarith only [P2a, h123_0, P1a, P0a, h012_0, htop]
        · linarith only [P1a, P2a, h123_0, P0a, h012_0, htop]
        · linarith only [htop, P2c, h013_2]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, d12lo, h012_0, P0a, htop, h013_2]
    · linarith only [d03hi, P0a, htop, d12lo, h012_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h012_2, P1a, h013_0, d13hi, d12lo]
      · linarith only [h013_2, d23hi, d12lo, h012_2, P1a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h013_2, P2a, htop, h123_3]
        · linarith only [h012_1, P0a, P2a, P1a, htop, h123_1, hn]
        · linarith only [htop, P2a, h013_2, h012_2]
        · linarith only [P2b, h123_1, h012_1, P0a, P1a, htop]
        · linarith only [h013_2, P2c, htop]
        · linarith only [htop, P2a, h123_1, P0a, P1a, h012_1]
  · linarith only [h013_2, h012_2, h123_1]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h013_0, h012_1, h023_1]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h012_3, P0a, h013_1]
    · linarith only [h023_0, P0a, h012_3, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h013_4]
      · linarith only [htop, h023_4, P1a]
      · linarith only [P1a, h013_2, htop, P0a, h023_2]
  · linarith only [h013_0, h123_0, h023_1]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, h023_0, d12lo, d01hi, P0a, htop, h123_2]
    · linarith only [P0a, h123_2, d12lo, htop, h023_2, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d13lo, P1a, htop, h012_1, d01hi, h023_2]
      · linarith only [htop, h123_2, P1a, d03hi, d12lo]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, h012_4, P2a, h123_1, htop]
        · linarith only [P2a, htop, P1a, hn, P0a]
        · linarith only [h123_2, P2a, htop, h012_1, h023_2]
        · linarith only [P2b, htop, P1a, P0a]
        · linarith only [htop, P2c, h012_1, h023_2, h123_1]
        · linarith only [P0a, P1a, htop, P2a]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, h012_1, htop]
    · linarith only [P0a, d01hi, h012_0, d23lo, h123_2, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, d01hi, htop, h013_2, d23lo]
      · linarith only [htop, h013_4, P1a]
      · linarith only [htop, h123_2, P1a, P0a, h012_2]
#print axioms upper_no_high_high_middle_031

theorem upper_no_high_high_middle_032 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d02 d03 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, P0a, d23hi, htop, h012_1, d01lo]
    · linarith only [htop, P0a, h012_0, h013_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h013_4, htop]
      · linarith only [d01lo, h123_0, d23hi, h012_2, P1a, htop]
      · linarith only [h123_2, P0a, htop, P1a, h012_2]
  · have G0 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, P0a, h023_2, d01lo, d12hi]
    · linarith only [htop, h012_0, P0a, h013_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_0, d12hi, h123_2, P1a, h012_0, d01lo, htop]
      · linarith only [d13hi, P1a, d01lo, h012_0, h023_2, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_0, h012_0, P2a, P0a, P1a, htop, hn]
        · linarith only [htop, h012_4, P2a, h023_2]
        · linarith only [h023_2, htop, P2a, h123_2]
        · linarith only [htop, P1a, h012_0, h123_0, P2a, P0a]
        · linarith only [h123_0, P1a, P0a, P2a, htop, h012_0]
        · linarith only [P2c, htop, h023_2]
  · linarith only [h123_0, h123_1, h012_1, h023_2]
  · have G0 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, h013_3, htop]
    · linarith only [P0a, h013_0, htop, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h023_4]
      · linarith only [h013_4, htop, P1a]
      · linarith only [h023_2, P0a, h013_2, P1a, htop]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h123_0, h012_2, h013_2]
  · have G0 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_0, d23lo, P0a, d12hi, h012_2, htop, h013_0]
    · linarith only [P0a, d02hi, h013_2, h123_0, d23lo, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d23lo, P1a, h013_2, htop, d01hi]
      · linarith only [d23lo, d12hi, h013_1, h123_0, htop, h012_2, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P0a, htop, hn, P2a, P1a]
        · linarith only [h012_0, htop, h123_3, h013_2, P2a]
        · linarith only [h013_2, h012_2, htop, h123_0, P2a]
        · linarith only [P0a, P1a, P2a, htop]
        · linarith only [P0a, P1a, htop, P2a]
        · linarith only [h012_0, h123_0, h013_2, htop, P2c]
  · have G0 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d12lo, h013_2, P0a, d13hi, h012_0]
    · linarith only [P0a, htop, d03hi, h012_2, d12lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h012_2, h013_0, d13hi, d12lo, P1a]
      · linarith only [h013_2, d12lo, h012_2, P1a, htop, d23hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h012_1, h013_2, h123_3, P2a]
        · linarith only [P0a, hn, P1a, P2a, htop]
        · linarith only [P2a, h123_1, h012_2, h013_2, htop]
        · linarith only [P1a, P2b, P0a, htop]
        · linarith only [htop, h012_1, P2c, h123_1, h013_2]
        · linarith only [P2a, P0a, htop, P1a]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h012_1, h013_0, h023_1]
  · have G0 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h013_1, P0a, h012_3]
    · linarith only [htop, P0a, h023_0, h012_3]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h013_4]
      · linarith only [P1a, htop, h023_4]
      · linarith only [htop, h023_2, h013_2, P0a, P1a]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h123_2, d12lo, d01hi, P0a, h023_0, htop, h012_1]
    · linarith only [htop, d01hi, P0a, h023_2, d12lo, h123_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, h012_1, d13lo, P1a, d01hi, h023_2]
      · linarith only [d12lo, htop, d03hi, P1a, h123_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h023_2, htop, h012_4, P2a]
        · linarith only [P2a, h123_1, htop, P1a, hn, P0a, h012_1]
        · linarith only [h023_2, h123_2, htop, P2a]
        · linarith only [htop, P1a, P2b, P0a, h123_1, h012_1]
        · linarith only [h023_2, P2c, htop]
        · linarith only [P2a, h012_1, P1a, htop, h123_1, P0a]
  · have G0 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, h013_3, htop, P0a]
    · linarith only [d23lo, h012_0, htop, h123_2, P0a, d01hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_2, htop, P1a, d23lo, d01hi]
      · linarith only [P1a, h013_4, htop]
      · linarith only [htop, P0a, P1a, h123_2, h012_2]
#print axioms upper_no_high_high_middle_032

theorem upper_no_high_high_middle_120 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d01 d02 d03 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d23hi, h123_2, d01lo, htop]
    · linarith only [P0a, htop, h012_2, d01lo, d13hi]
    · linarith only [h012_2, htop, h123_0, P0a]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_1, h012_4, P1a, h123_0, htop]
      · linarith only [h023_2, htop, P1a, h012_4]
      · linarith only [htop, h123_1, P1a, h123_0, h023_2]
    · linarith only [h023_2, d01lo, d12hi, P0a, h012_0, htop, h123_0]
    · linarith only [h012_0, h123_2, h023_2, P0a, htop]
  · linarith only [h023_2, h123_0, h123_1, h012_1]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h012_3, P0a, h123_4, htop]
      · linarith only [P1a, h023_2, d01lo, h123_4, d12hi, htop, P0a]
      · linarith only [P1a, h012_1, htop, h023_2]
    · linarith only [h013_2, d01lo, P0a, htop, d12hi]
    · linarith only [h012_2, P0a, htop]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h023_0, h012_0, h013_1]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, h012_2, d12hi, P0a, htop, h123_0]
    · linarith only [h123_0, d23lo, P0a, d12hi, h013_2, htop]
    · linarith only [htop, h012_2, P0a, h013_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d13hi, htop, d12lo, h013_2]
    · linarith only [d12lo, P0a, d13hi, htop, h012_2]
    · linarith only [P0a, htop, h013_2, h012_2]
  · linarith only [h012_2, h123_1, h013_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, P0a, htop, d01hi, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, d23hi, h023_2, P1a, htop]
      · linarith only [h012_3, P1a, htop, h123_4, P0a]
      · linarith only [P1a, h012_3, P0a, h123_0, h023_2, htop]
    · linarith only [h013_2, htop, h123_0, P0a]
  · linarith only [h023_1, h013_0, h123_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, d01hi, h023_2, P0a, h012_1, h123_1, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d12lo, h023_2, d02hi, P1a, htop]
      · linarith only [P1a, h123_2, d02hi, d12lo, htop]
      · linarith only [htop, h123_2, h023_2, P1a]
    · linarith only [htop, h123_2, P0a, h023_2, h012_1]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h012_2, d01hi, h123_0, d23lo]
    · linarith only [h123_2, d01hi, d23lo, htop, P0a]
    · linarith only [h013_2, htop, P0a]
#print axioms upper_no_high_high_middle_120

theorem upper_no_high_high_middle_123 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d02 d12 d23 t))
    (P2 : Middle n (sortedGaps d03 d13 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h123_2, d23hi, d01lo, P0a]
    · linarith only [d01lo, h012_2, P0a, d13hi, htop]
    · linarith only [htop, h012_2, P0a, h123_0]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h123_1, h123_0, h012_4]
      · linarith only [h012_4, htop, h023_2, P1a]
      · linarith only [htop, h023_2, h123_0, h123_1, P1a]
    · linarith only [d12hi, htop, h023_2, P0a, h123_0, d01lo, h012_0]
    · linarith only [h012_0, P0a, h023_2, h123_2, htop]
  · linarith only [h012_1, h123_1, h123_0, h023_2]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_4, P1a, h012_3, P0a, htop]
      · linarith only [h123_4, P0a, htop, d01lo, h023_2, d12hi, P1a]
      · linarith only [P1a, h023_2, h012_1, htop]
    · linarith only [d01lo, d12hi, h013_2, htop, P0a]
    · linarith only [h012_2, htop, P0a]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h023_0, h013_1, h012_0]
  · linarith only [h123_0, h012_2, h013_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12hi, htop, h012_2, d23lo, P0a, h123_0]
    · linarith only [htop, h123_0, d23lo, h013_2, d12hi, P0a]
    · linarith only [h012_2, h013_2, P0a, htop]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, h013_2, d12lo, P0a, htop]
    · linarith only [h012_2, htop, P0a, d12lo, d13hi]
    · linarith only [P0a, h013_2, htop, h012_2]
  · linarith only [h013_2, h012_2, h123_1]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h012_1, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, P0a, d01hi, d12lo, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, d12lo, d23hi, h023_2, htop]
      · linarith only [P0a, htop, P1a, h123_4, h012_3]
      · linarith only [h123_0, P1a, P0a, htop, h023_2, h012_3]
    · linarith only [h123_0, htop, P0a, h013_2]
  · linarith only [h023_1, h123_0, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h023_2, d12lo, P0a, htop, h123_1, d01hi, h012_1]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_2, P1a, d02hi, htop, d12lo]
      · linarith only [P1a, d02hi, d12lo, htop, h123_2]
      · linarith only [h123_2, htop, h023_2, P1a]
    · linarith only [htop, h012_1, h123_2, P0a, h023_2]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, h123_0, d23lo, d01hi, P0a, htop]
    · linarith only [P0a, htop, d23lo, h123_2, d01hi]
    · linarith only [htop, h013_2, P0a]
#print axioms upper_no_high_high_middle_123

theorem upper_no_high_high_middle_130 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d01 d02 d03 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, htop, h123_2, d01lo, d23hi]
    · linarith only [d13hi, P0a, d01lo, h012_2, htop]
    · linarith only [h012_2, htop, P0a, h123_0]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h023_4, htop]
      · linarith only [P1a, h123_1, h012_4, h023_2, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_2, P2a, h023_2, d01lo, htop, d12hi]
        · linarith only [h123_2, h023_1, htop, h012_4, P2a]
        · linarith only [P2a, P0a, hn, htop, P1a]
        · linarith only [d12hi, P2c, htop, d01lo, h023_1, h123_2]
        · linarith only [P0a, P2b, htop, P1a]
        · linarith only [P2b, P0a, P1a, htop]
    · linarith only [d01lo, P0a, h023_2, h123_0, d12hi, h012_0, htop]
    · linarith only [h123_2, P0a, h023_2, h012_0, htop]
  · linarith only [h023_2, h123_0, h123_1, h012_1]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h123_4, P1a, h013_1, htop]
      · linarith only [h023_0, htop, P1a, h123_4]
      · linarith only [P0a, h012_3, P1a, h023_2, htop]
    · linarith only [d01lo, d12hi, h013_2, P0a, htop]
    · linarith only [P0a, h012_2, htop]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h012_2, h123_0, h013_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d23lo, htop, h012_2, d12hi, h123_0]
    · linarith only [h013_2, d23lo, P0a, d12hi, h123_0, htop]
    · linarith only [P0a, h012_2, htop, h013_2]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [P0a, d13hi, htop, h013_2, d12lo]
    · linarith only [h012_2, htop, P0a, d13hi, d12lo]
    · linarith only [h013_2, htop, P0a, h012_2]
  · linarith only [h013_2, h123_1, h012_2]
  · linarith only [h013_0, h012_1, h023_1]
  · linarith only [h013_0, h023_1, h012_1]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, P0a, h013_2, d12lo, htop]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h013_4]
      · linarith only [P1a, htop, h023_4]
      · linarith only [P0a, h023_2, htop, P1a, h012_3]
    · linarith only [P0a, h013_2, htop, h123_0]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, h012_1, htop, P0a, d12lo, h023_2, h123_1]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_2, d13lo, P1a, htop, d02hi]
      · linarith only [htop, P1a, h123_2, d12lo, d03hi]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_2, P2a, h012_4, h023_0, htop]
        · linarith only [htop, P2a, h023_2, h123_2, d12lo, d01hi]
        · linarith only [htop, P1a, hn, P2a, P0a]
        · linarith only [d12lo, P2c, h023_0, h123_2, d01hi, htop]
        · linarith only [P0a, htop, P1a, P2b]
        · linarith only [P1a, P2b, htop, P0a]
    · linarith only [h023_2, P0a, h123_2, h012_1, htop]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_2, d01hi, d23lo, P0a, htop, h123_0]
    · linarith only [h123_2, d23lo, htop, d01hi, P0a]
    · linarith only [P0a, h013_2, htop]
#print axioms upper_no_high_high_middle_130

theorem upper_no_high_high_middle_132 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d01 d12 d13 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d02 d12 d23 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, d23hi, htop, P0a, h123_2]
    · linarith only [P0a, d01lo, htop, h012_2, d13hi]
    · linarith only [h012_2, P0a, h123_0, htop]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, h023_4, htop]
      · linarith only [htop, h012_4, P1a, h123_1, h023_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_2, htop, P2a, h012_4]
        · linarith only [P1a, P0a, htop, d01lo, P2a, h023_1, hn, d12hi]
        · linarith only [h023_2, h123_2, P2a, htop]
        · linarith only [d12hi, P1a, d01lo, P0a, P2b, h023_1, htop]
        · linarith only [h123_2, P2c, htop]
        · linarith only [P0a, d12hi, h023_1, P1a, P2a, htop, d01lo]
    · linarith only [h123_0, d01lo, htop, h012_0, d12hi, h023_2, P0a]
    · linarith only [P0a, h012_0, htop, h023_2, h123_2]
  · linarith only [h012_1, h123_0, h123_1, h023_2]
  · have G0 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_1, h123_4, htop, P1a]
      · linarith only [h123_4, htop, P1a, h023_0]
      · linarith only [h023_2, P1a, htop, P0a, h012_3]
    · linarith only [d01lo, P0a, h013_2, d12hi, htop]
    · linarith only [h012_2, htop, P0a]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h013_1, h023_0, h012_0]
  · linarith only [h013_2, h123_0, h012_2]
  · have G0 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, h123_0, P0a, htop, d12hi, h012_2]
    · linarith only [P0a, h013_2, h123_0, d23lo, d12hi, htop]
    · linarith only [h012_2, h013_2, P0a, htop]
  · have G0 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, d13hi, P0a, h013_2, d12lo]
    · linarith only [d13hi, htop, d12lo, P0a, h012_2]
    · linarith only [htop, h012_2, P0a, h013_2]
  · linarith only [h012_2, h123_1, h013_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h012_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, P0a, htop, d01hi, h013_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h013_4]
      · linarith only [h023_4, P1a, htop]
      · linarith only [h012_3, h023_2, P1a, P0a, htop]
    · linarith only [h123_0, h013_2, htop, P0a]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_1, d01hi, htop, d12lo, h023_2, h123_1, P0a]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_2, htop, d02hi, d13lo, P1a]
      · linarith only [h123_2, d12lo, d03hi, P1a, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, h023_0, d12lo, P2a, P1a, d01hi, P0a, hn]
        · linarith only [htop, h123_2, P2a, h012_4]
        · linarith only [htop, h123_2, P2a, h023_2]
        · linarith only [htop, d12lo, h023_0, P0a, d01hi, P2a, P1a]
        · linarith only [P0a, d12lo, d01hi, htop, P2a, P1a, h023_0]
        · linarith only [htop, h123_2, P2c]
    · linarith only [h023_2, P0a, h123_2, htop, h012_1]
  · have G0 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, h123_0, htop, P0a, d01hi, h012_2]
    · linarith only [P0a, h123_2, d23lo, htop, d01hi]
    · linarith only [P0a, htop, h013_2]
#print axioms upper_no_high_high_middle_132

theorem upper_no_high_high_middle_230 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d01 d02 d03 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_0, d01lo, P0a, d23hi, h123_2, htop]
    · linarith only [d23hi, d01lo, P0a, h012_2, htop]
    · linarith only [h123_2, h012_1, P0a, htop]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d02 d03 t (by linarith only [h012_0]) (by linarith only [h023_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [h012_0, h123_2, d01lo, d12hi, htop, P0a]
    · linarith only [htop, d01lo, h023_2, h012_0, d12hi, P0a]
    · linarith only [h023_2, P0a, htop, h123_2]
  · linarith only [h123_1, h123_0, h012_1, h023_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d02 d03 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, P1a, h023_4]
      · linarith only [h013_4, htop, P1a]
      · linarith only [htop, P1a, h013_2, P0a, h012_3]
    · linarith only [h023_2, P0a, d12hi, d23lo, htop]
    · linarith only [h023_2, P0a, htop, h012_1]
  · linarith only [h012_0, h023_0, h013_1]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h012_2, h013_2, h123_0]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d02 d03 t (by linarith only [h013_1]) (by linarith only [h012_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [d01hi, htop, P1a, d23lo, h013_2]
      · linarith only [h012_1, P1a, h123_3, htop, h012_0, h013_1]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [htop, P2a, h012_2, h123_3, h013_0]
        · linarith only [htop, h123_3, h012_1, h013_2, P2a]
        · linarith only [P2a, htop, P1a, hn, P0a]
        · linarith only [h123_3, h012_1, htop, P2c, h013_0]
        · linarith only [htop, P2b, P1a, P0a]
        · linarith only [P2b, P0a, P1a, htop]
    · linarith only [d12hi, h123_0, d23lo, h013_2, P0a, htop, h012_0]
    · linarith only [htop, h123_0, P0a, h013_2, h012_2]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d02 d03 t (by linarith only [h012_1]) (by linarith only [h013_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d13hi, h012_1, htop, h013_2, P0a, d12lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h012_2, d12lo, d13hi, h013_0]
      · linarith only [P1a, h013_2, d23hi, htop, d12lo, h012_2]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_3, P2a, h013_2, h012_0, htop]
        · linarith only [htop, h123_3, h013_1, P2a, h012_2]
        · linarith only [P2a, P0a, P1a, htop, hn]
        · linarith only [P2c, h012_0, h013_1, htop, h123_3]
        · linarith only [P1a, htop, P0a, P2b]
        · linarith only [htop, P2b, P0a, P1a]
    · linarith only [h013_2, htop, h012_2, h123_1, P0a]
  · linarith only [h123_1, h012_2, h013_2]
  · linarith only [h023_1, h013_0, h012_1]
  · linarith only [h012_1, h013_0, h023_1]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d02 d03 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, d12lo, htop, P0a, h023_2]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h013_1, htop, h123_4, h012_3, P1a, P0a]
      · linarith only [h013_0, htop, P1a, h123_4]
      · linarith only [h013_2, P0a, htop, h012_3, P1a]
    · linarith only [P0a, htop, h023_2, h012_0]
  · linarith only [h013_0, h023_1, h123_0]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, htop, d12lo, h023_2, P0a, h012_1]
    · linarith only [h012_1, h123_2, htop, d12lo, d01hi, P0a]
    · linarith only [h123_2, htop, P0a, h023_2]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d02 d03 t (by linarith only [h023_1]) (by linarith only [h012_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, P0a, htop, h012_2, d01hi]
    · linarith only [d23lo, d02hi, h123_2, htop, P0a]
    · linarith only [htop, h123_2, h012_0, P0a]
#print axioms upper_no_high_high_middle_230

theorem upper_no_high_high_middle_231 (n t d01 d02 d03 d12 d13 d23 : ℝ)
    (hn : 3 ≤ n) (ht : n ≤ t)
    (htop : t < n + 1)
    (hhalf : n + 1/2 ≤ t)
    (rd01 : 0 ≤ d01 ∧ d01 < t)
    (rd02 : 0 ≤ d02 ∧ d02 < t)
    (rd03 : 0 ≤ d03 ∧ d03 < t)
    (rd12 : 0 ≤ d12 ∧ d12 < t)
    (rd13 : 0 ≤ d13 ∧ d13 < t)
    (rd23 : 0 ≤ d23 ∧ d23 < t)
    (h012 : TripleCap d01 d02 d12 t)
    (h013 : TripleCap d01 d03 d13 t)
    (h023 : TripleCap d02 d03 d23 t)
    (h123 : TripleCap d12 d13 d23 t)
    (P0 : High n (sortedGaps d02 d12 d23 t))
    (P1 : High n (sortedGaps d03 d13 d23 t))
    (P2 : Middle n (sortedGaps d01 d12 d13 t))
    : False := by
  obtain ⟨d01lo, d01hi⟩ := rd01
  obtain ⟨d02lo, d02hi⟩ := rd02
  obtain ⟨d03lo, d03hi⟩ := rd03
  obtain ⟨d12lo, d12hi⟩ := rd12
  obtain ⟨d13lo, d13hi⟩ := rd13
  obtain ⟨d23lo, d23hi⟩ := rd23
  rcases h012 with ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩ | ⟨h012_0, h012_1, h012_2, h012_3, h012_4⟩
  all_goals rcases h013 with ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩ | ⟨h013_0, h013_1, h013_2, h013_3, h013_4⟩
  all_goals rcases h023 with ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩ | ⟨h023_0, h023_1, h023_2, h023_3, h023_4⟩
  all_goals rcases h123 with ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩ | ⟨h123_0, h123_1, h123_2, h123_3, h123_4⟩
  · have G0 := sortedGaps_order_012 d02 d12 d23 t (by linarith only [h012_1]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_012 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h123_0])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23hi, d01lo, h012_0, h123_2, htop, P0a]
    · linarith only [P0a, h012_2, d01lo, d23hi, htop]
    · linarith only [h012_1, htop, P0a, h123_2]
  · have G0 := sortedGaps_order_021 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h123_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_021 d03 d13 d23 t (by linarith only [h023_1]) (by linarith only [h123_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01lo, htop, P0a, h012_0, d12hi, h123_2]
    · linarith only [d01lo, P0a, h023_2, d12hi, h012_0, htop]
    · linarith only [h023_2, h123_2, htop, P0a]
  · linarith only [h012_1, h123_1, h123_0, h023_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_201 d03 d13 d23 t (by linarith only [h023_0]) (by linarith only [h013_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_021 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h123_1])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [h023_4, htop, P1a]
      · linarith only [h013_4, htop, P1a]
      · linarith only [h013_2, htop, P1a, h012_3, P0a]
    · linarith only [h023_2, d23lo, d12hi, htop, P0a]
    · linarith only [h012_1, htop, P0a, h023_2]
  · linarith only [h013_1, h012_0, h023_0]
  · linarith only [h012_0, h013_1, h023_0]
  · linarith only [h123_0, h013_2, h012_2]
  · have G0 := sortedGaps_order_201 d02 d12 d23 t (by linarith only [h023_2]) (by linarith only [h012_1])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_201 d01 d12 d13 t (by linarith only [h013_2]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · rcases P1 with P1a | P1a | P1a
      · linarith only [htop, d23lo, d01hi, P1a, h013_2]
      · linarith only [h123_3, h012_0, h012_1, P1a, h013_1, htop]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [P2a, htop, h012_2, h123_3]
        · linarith only [htop, h013_2, P2a, h123_3]
        · linarith only [P0a, h013_0, P2a, htop, h012_1, P1a, hn]
        · linarith only [htop, P2c, h123_3]
        · linarith only [P2b, P0a, h013_0, P1a, h012_1, htop]
        · linarith only [h013_0, P2b, P1a, P0a, h012_1, htop]
    · linarith only [h012_0, h013_2, P0a, d23lo, htop, h123_0, d12hi]
    · linarith only [h123_0, htop, P0a, h013_2, h012_2]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_012 d03 d13 d23 t (by linarith only [h013_1]) (by linarith only [h123_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_102 d01 d12 d13 t (by linarith only [h012_2]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [htop, h012_1, h013_2, d13hi, P0a, d12lo]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P1a, htop, h013_0, h012_2, d12lo, d13hi]
      · linarith only [d23hi, h012_2, d12lo, h013_2, htop, P1a]
      · rcases P2 with P2a | P2a | P2a | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩ | ⟨P2a, P2b, P2c⟩
        · linarith only [h123_3, P2a, h013_2, htop]
        · linarith only [htop, h012_2, P2a, h123_3]
        · linarith only [P0a, h013_1, P2a, htop, P1a, h012_0, hn]
        · linarith only [h123_3, P2c, htop]
        · linarith only [htop, h013_1, P1a, P2b, h012_0, P0a]
        · linarith only [h013_1, htop, P1a, P2b, h012_0, P0a]
    · linarith only [P0a, h123_1, htop, h013_2, h012_2]
  · linarith only [h013_2, h123_1, h012_2]
  · linarith only [h012_1, h013_0, h023_1]
  · linarith only [h023_1, h013_0, h012_1]
  · have G0 := sortedGaps_order_102 d02 d12 d23 t (by linarith only [h012_0]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_102 d03 d13 d23 t (by linarith only [h013_0]) (by linarith only [h023_1])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d12lo, P0a, htop, h023_2, d23hi]
    · rcases P1 with P1a | P1a | P1a
      · linarith only [P0a, h012_3, htop, P1a, h123_4, h013_1]
      · linarith only [h123_4, P1a, h013_0, htop]
      · linarith only [P0a, htop, h013_2, P1a, h012_3]
    · linarith only [h023_2, P0a, htop, h012_0]
  · linarith only [h123_0, h023_1, h013_0]
  · have G0 := sortedGaps_order_120 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h023_2])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_120 d03 d13 d23 t (by linarith only [h123_1]) (by linarith only [h023_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_120 d01 d12 d13 t (by linarith only [h123_0]) (by linarith only [h013_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d01hi, P0a, h023_2, d12lo, h012_1, htop]
    · linarith only [htop, h012_1, d01hi, P0a, d12lo, h123_2]
    · linarith only [h023_2, h123_2, htop, P0a]
  · have G0 := sortedGaps_order_210 d02 d12 d23 t (by linarith only [h123_2]) (by linarith only [h012_0])
    rw [G0] at P0
    simp only [High] at P0
    have G1 := sortedGaps_order_210 d03 d13 d23 t (by linarith only [h123_0]) (by linarith only [h013_0])
    rw [G1] at P1
    simp only [High] at P1
    have G2 := sortedGaps_order_210 d01 d12 d13 t (by linarith only [h123_1]) (by linarith only [h012_2])
    rw [G2] at P2
    simp only [Middle] at P2
    rcases P0 with P0a | P0a | P0a
    · linarith only [d23lo, htop, h012_2, d01hi, P0a]
    · linarith only [d02hi, d23lo, h123_2, htop, P0a]
    · linarith only [h012_0, h123_2, htop, P0a]
#print axioms upper_no_high_high_middle_231

end JSP404.FourCenter
