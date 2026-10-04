import GlobalDirections
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.List.Sort

/-!
A five-center counterexample to capacity-preserving deletion in the direction
relaxation. Directions are measured in units of 1/24, with period 84/24=7/2.
The same directions satisfy all fields of the arbitrary-center Model.

For each vertex we sort its incident unoriented directions and use the cyclic
gaps. Integer division by 24 computes the normalized gap floors exactly.
Total weight is 8, but deleting any vertex leaves weight 7. Thus an induction
that demands a capacity-preserving single-vertex deletion is invalid for this
model. This does NOT refute the Sendov bound (which is 10 at this period), and
Euclidean realizability of this abstract model is not asserted.
-/
namespace JSP404.FiniteReductionCounterexample

def units : Fin 5 → Fin 5 → ℕ :=
  ![![0,58,33,69,46], ![58,0,32,82,34], ![33,32,0,83,81],
    ![69,82,83,0,21], ![46,34,81,21,0]]

def vertices : List (Fin 5) := [0,1,2,3,4]

def incident (S : List (Fin 5)) (i : Fin 5) : List ℕ :=
  ((S.erase i).map (units i)).insertionSort (· ≤ ·)

def cyclicGaps (ds : List ℕ) : List ℕ :=
  match ds with
  | [] => []
  | x :: xs => ((x :: xs).zip xs).map (fun ab ↦ ab.2-ab.1) ++
      [84+x-(x :: xs).getLast!]

def exponent (S : List (Fin 5)) (i : Fin 5) : ℕ :=
  ((cyclicGaps (incident S i)).map (fun g ↦ g/24-1)).sum

def capacity (S : List (Fin 5)) : ℕ :=
  (S.map (fun i ↦ 2 ^ exponent S i)).sum

theorem scaled_gap_floor (g : ℕ) : Nat.floor ((g : ℝ)/24) = g/24 := by
  simpa using Nat.floor_div_natCast (g : ℝ) 24

noncomputable def witnessModel : GlobalDirections.Model 5 (7/2) where
  direction i j := (units i j : ℝ)/24
  range := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num [units] at *
  triangle := by
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [units, FourCenter.TripleCap] at *

theorem vertices_nodup : vertices.Nodup := by decide

theorem full_capacity_eight : capacity vertices = 8 := by decide +kernel

theorem every_deletion_capacity_seven :
    ∀ i : Fin 5, capacity (vertices.erase i) = 7 := by decide +kernel

theorem no_capacity_preserving_deletion :
    ¬ ∃ i : Fin 5, capacity vertices ≤ capacity (vertices.erase i) := by
  simp only [full_capacity_eight, every_deletion_capacity_seven]
  omega

#print axioms witnessModel
#print axioms scaled_gap_floor
#print axioms vertices_nodup
#print axioms full_capacity_eight
#print axioms every_deletion_capacity_seven
#print axioms no_capacity_preserving_deletion
end JSP404.FiniteReductionCounterexample
