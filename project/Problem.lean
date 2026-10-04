import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
JSP-000404 / Erdos 504: the complete research target, not an asserted theorem.
The formulas follow Sendov, Acta Math. Hungar. 69 (1995), Theorem 4.1,
printed page 42. In the smaller interval the numerator is TWO.
No third-party Lean proof source is imported by this project.
-/
namespace JSP404

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Every configuration of n distinct points determines an angle at least a. -/
def Unavoidable (n : ℕ) (a : ℝ) : Prop :=
  ∀ p : Fin n → Plane, Function.Injective p →
    ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧
      a ≤ EuclideanGeometry.angle (p i) (p j) (p k)

/-- Arbitrarily close upper constructions, with no attainment assumption. -/
def ApproximableCap (n : ℕ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ p : Fin n → Plane, Function.Injective p ∧
    ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      EuclideanGeometry.angle (p i) (p j) (p k) ≤ a + ε

/-- Lower and upper assertions needed to determine the extremal value. -/
def ExactValue (n : ℕ) (a : ℝ) : Prop :=
  Unavoidable n a ∧ ApproximableCap n a

noncomputable def firstValue (m : ℕ) : ℝ := Real.pi * (1 - 2 / (2 * (m : ℝ) + 1))
noncomputable def secondValue (m : ℕ) : ℝ := Real.pi * (1 - 1 / ((m : ℝ) + 1))
def transition (m : ℕ) : ℕ := 2 ^ m + 2 ^ (m - 2)

/-- Complete proposed classification for all n >= 3. NOT proved here. -/
def FullClassification : Prop :=
  ExactValue 3 (Real.pi / 3) ∧
  ExactValue 4 (Real.pi / 2) ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, 2 ^ m < n → n ≤ transition m →
    ExactValue n (firstValue m)) ∧
  (∀ m : ℕ, 2 ≤ m → ∀ n : ℕ, transition m < n → n ≤ 2 ^ (m + 1) →
    ExactValue n (secondValue m))

/-- The two infinite families that remain the main lower-bound research target. -/
def ThresholdLowerBounds : Prop :=
  (∀ m : ℕ, 2 ≤ m → Unavoidable (2 ^ m + 1) (firstValue m)) ∧
  (∀ m : ℕ, 2 ≤ m → Unavoidable (transition m + 1) (secondValue m))

end JSP404
