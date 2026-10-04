import FourCenterCapacity
import FourCenterWeights

/-!
Correct four-center capacity inequalities for every integer n >= 3, in the
explicit necessary direction model. These statements cover four centers only.
They do not prove a bound for an arbitrary number of centers or a complete
Euclidean solution of Erdos 504.
-/
namespace JSP404.FourCenter

theorem capacity_bound_lower (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (ht : (n : ℝ) ≤ t) (htop : t < (n : ℝ)+1/2)
    (M : DirectionModel t) (C : ∀ i : Fin 4, CapacityData (M.gaps i)) :
    ∑ i : Fin 4, 2^(C i).exponent ≤ 2^n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hbudget : ∀ i, (C i).a+(C i).b+(C i).c ≤ n :=
    fun i ↦ (C i).floor_budget (M.gaps_sum i) (by linarith)
  apply four_weight_lower n hn (fun i ↦ (C i).exponent)
  · intro i
    exact (C i).exponent_le (by omega) (hbudget i)
  · intro i j hij hi hj
    exact no_two_high_lower hnR ht htop M i j hij
      ((C i).high_of_exponent hn (hbudget i) hi)
      ((C j).high_of_exponent hn (hbudget j) hj)
  · intro i j k hij hik hjk hi hj hk
    exact no_high_two_middle_lower hnR ht htop M i j k hij hik hjk
      ((C i).high_of_exponent hn (hbudget i) hi)
      ((C j).middle_of_exponent hn (hbudget j) hj)
      ((C k).middle_of_exponent hn (hbudget k) hk)

theorem capacity_bound_upper (n : ℕ) (hn : 3 ≤ n) (t : ℝ)
    (ht : (n : ℝ) ≤ t) (htop : t < (n : ℝ)+1) (hhalf : (n : ℝ)+1/2 ≤ t)
    (M : DirectionModel t) (C : ∀ i : Fin 4, CapacityData (M.gaps i)) :
    ∑ i : Fin 4, 2^(C i).exponent ≤ 2^n+2^(n-2) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hbudget : ∀ i, (C i).a+(C i).b+(C i).c ≤ n :=
    fun i ↦ (C i).floor_budget (M.gaps_sum i) htop
  apply four_weight_upper n hn (fun i ↦ (C i).exponent)
  · intro i
    exact (C i).exponent_le (by omega) (hbudget i)
  · intro i j k hij hik hjk hi hj hk
    exact no_two_high_middle_upper hnR ht htop hhalf M i j k hij hik hjk
      ((C i).high_of_exponent hn (hbudget i) hi)
      ((C j).high_of_exponent hn (hbudget j) hj)
      ((C k).middle_of_exponent hn (hbudget k) hk)

#check @capacity_bound_lower
#check @capacity_bound_upper
#print axioms capacity_bound_lower
#print axioms capacity_bound_upper
end JSP404.FourCenter
