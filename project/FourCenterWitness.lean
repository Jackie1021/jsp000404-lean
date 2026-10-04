import FourCenterBound

namespace JSP404.FourCenter

/-- A rational, consistent direction-model instance. This is a model witness;
no assertion of exact Euclidean realization of these rational angles is made. -/
noncomputable def witnessModel : DirectionModel (15/4) where
  d01 := 23/10
  d02 := 12/5
  d03 := 7/4
  d12 := 29/8
  d13 := 6/5
  d23 := 11/10
  r01 := by norm_num
  r02 := by norm_num
  r03 := by norm_num
  r12 := by norm_num
  r13 := by norm_num
  r23 := by norm_num
  c012 := by norm_num [TripleCap]
  c013 := by norm_num [TripleCap]
  c023 := by norm_num [TripleCap]
  c123 := by norm_num [TripleCap]

noncomputable def witnessCapacity (i : Fin 4) : CapacityData (witnessModel.gaps i) where
  a := ![0,1,1,0] i
  b := ![0,1,1,0] i
  c := ![3,1,1,3] i
  a_lo := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]
  b_lo := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]
  c_lo := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]
  a_hi := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]
  b_hi := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]
  c_hi := by fin_cases i <;> norm_num [DirectionModel.gaps,witnessModel,sortedGaps,min_def,max_def]

theorem witness_weight_ten : ∑ i : Fin 4, 2^(witnessCapacity i).exponent = 10 := by
  norm_num [Fin.sum_univ_succ,witnessCapacity,CapacityData.exponent]

theorem witness_attains_upper_capacity :
    (∑ i : Fin 4, 2^(witnessCapacity i).exponent) ≤ 2^3+2^(3-2) := by
  exact capacity_bound_upper 3 (by omega) (15/4) (by norm_num) (by norm_num)
    (by norm_num) witnessModel witnessCapacity

theorem witness_exceeds_nine : 9 < ∑ i : Fin 4, 2^(witnessCapacity i).exponent := by
  rw [witness_weight_ten]
  omega

#print axioms witness_weight_ten
#print axioms witness_attains_upper_capacity
#print axioms witness_exceeds_nine
end JSP404.FourCenter
