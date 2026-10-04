import Reduction
import FourCenterBound
import FourCenterWitness

/-!
Coverage audit only: six obligations are equivalent to the complete target.
This file does NOT supply those obligations and does NOT solve JSP-000404.
The equivalence is an acceptance contract, not new progress on the missing
geometric lower bounds.
-/
namespace JSP404.CoverageAudit

def LowerFirst : Prop :=
  ∀ m : ℕ, 2 ≤ m → Unavoidable (2 ^ m + 1) (firstValue m)
def LowerSecond : Prop :=
  ∀ m : ℕ, 2 ≤ m → Unavoidable (transition m + 1) (secondValue m)
def UpperFirst : Prop :=
  ∀ m : ℕ, 2 ≤ m → ApproximableCap (transition m) (firstValue m)
def UpperSecond : Prop :=
  ∀ m : ℕ, 2 ≤ m → ApproximableCap (2 ^ (m + 1)) (secondValue m)

def CompleteObligations : Prop :=
  ExactValue 3 (Real.pi / 3) ∧ ExactValue 4 (Real.pi / 2) ∧
  LowerFirst ∧ LowerSecond ∧ UpperFirst ∧ UpperSecond

private theorem transition_bounds (m : ℕ) (hm : 2 ≤ m) :
    2 ^ m < transition m ∧ transition m < 2 ^ (m + 1) := by
  have hpos : 0 < 2 ^ (m - 2) := pow_pos (by decide) _
  have hlt : 2 ^ (m - 2) < 2 ^ m :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  simp only [transition, pow_succ]
  omega

/-- Exactly the mathematical obligations required to complete this target.
The left side is NOT proved by the existing project. -/
theorem fullClassification_iff_completeObligations :
    FullClassification ↔ CompleteObligations := by
  constructor
  · rintro ⟨h3, h4, hFirst, hSecond⟩
    refine ⟨h3, h4, ?_, ?_, ?_, ?_⟩
    · intro m hm
      have ht := transition_bounds m hm
      exact (hFirst m hm (2 ^ m + 1) (by omega) (by omega)).1
    · intro m hm
      have ht := transition_bounds m hm
      exact (hSecond m hm (transition m + 1) (by omega) (by omega)).1
    · intro m hm
      have ht := transition_bounds m hm
      exact (hFirst m hm (transition m) ht.1 le_rfl).2
    · intro m hm
      have ht := transition_bounds m hm
      exact (hSecond m hm (2 ^ (m + 1)) ht.2 le_rfl).2
  · rintro ⟨h3, h4, hLF, hLS, hUF, hUS⟩
    exact classification_of_thresholds h3 h4 ⟨hLF, hLS⟩ hUF hUS

/-- A geometric lower bound must exclude every configuration whose actual
angles are strictly below the claimed threshold. No capacity surrogate occurs
in this equivalent statement. -/
theorem unavoidable_iff_no_strict_cap (n : ℕ) (a : ℝ) :
    Unavoidable n a ↔
      ∀ p : Fin n → Plane, Function.Injective p →
        ¬ (∀ i j k, i ≠ j → j ≠ k → i ≠ k →
          EuclideanGeometry.angle (p i) (p j) (p k) < a) := by
  classical
  simp only [Unavoidable]
  push Not
  rfl

#check fullClassification_iff_completeObligations
#print axioms fullClassification_iff_completeObligations
#check unavoidable_iff_no_strict_cap
#print axioms unavoidable_iff_no_strict_cap
#check classification_of_thresholds
#check JSP404.FourCenter.capacity_bound_lower
#check JSP404.FourCenter.capacity_bound_upper
#print FullClassification
#print CompleteObligations

end JSP404.CoverageAudit
