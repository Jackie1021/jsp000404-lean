import Mathlib.Tactic

/-! Exact integer arithmetic for a ten-point regression configuration.
This is NOT a new solution, NOT an angle-geometry theorem, and NOT an award
claim. Its purpose is to test a proposed repair to the four-center argument.
The algebraic predicate below is the squared cosine test for cos(angle) >= -2/3.
The formal bridge to EuclideanGeometry.angle is not claimed in this file.
-/
namespace JSP404.Regression

abbrev ZPoint := ℤ × ℤ
def points : Fin 10 → ZPoint := ![
  (-1000995, -6006), (-1001005, -5994), (-998995, 5994), (-999005, 6006),
  (995001, -6006), (994999, -5994), (1005001, 5994), (1004999, 6006),
  (0, 500000), (0, 600000)]

def dotAt (p q r : ZPoint) : ℤ :=
  (p.1 - q.1) * (r.1 - q.1) + (p.2 - q.2) * (r.2 - q.2)
def distSq (p q : ZPoint) : ℤ := (p.1 - q.1)^2 + (p.2 - q.2)^2
abbrev CosineCertificate (p q r : ZPoint) : Prop :=
  0 ≤ dotAt p q r ∨ 9 * (dotAt p q r)^2 ≤ 4 * distSq p q * distSq r q

def cluster (i : Fin 10) : ℕ :=
  if i.val < 4 then 0 else if i.val < 8 then 1 else i.val - 6

def center (i : ℕ) : ZPoint :=
  if i = 0 then (-10, 0) else if i = 1 then (10, 0)
  else if i = 2 then (0, 5) else (0, 6)

/-- A finite direction table for two perfect four-leaf clusters and two
singletons. This is not a formal definition of all generalized configurations. -/
def generalizedDirection (i j : Fin 10) : ZPoint :=
  if cluster i ≠ cluster j then
    ((center (cluster j)).1 - (center (cluster i)).1,
     (center (cluster j)).2 - (center (cluster i)).2)
  else
    let high : ℤ := (j.val % 4 / 2 : ℕ) - (i.val % 4 / 2 : ℕ)
    let low : ℤ := (j.val % 2 : ℕ) - (i.val % 2 : ℕ)
    let v : ZPoint := if cluster i = 0 then (1, 6) else (5, 6)
    let w : ZPoint := if cluster i = 0 then (-5, 6) else (-1, 6)
    if high ≠ 0 then (high * v.1, high * v.2) else (low * w.1, low * w.2)

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem points_distinct : Function.Injective points := by decide

theorem all_integer_certificates :
    ∀ i j k : Fin 10, CosineCertificate (points i) (points j) (points k) := by
  decide +kernel

theorem all_generalized_certificates :
    ∀ i j k : Fin 10, CosineCertificate
      (generalizedDirection j i) (0, 0) (generalizedDirection j k) := by
  decide +kernel

theorem generalized_nonzero :
    ∀ i j : Fin 10, i ≠ j → generalizedDirection i j ≠ (0, 0) := by
  decide +kernel

#print axioms points_distinct
#print axioms all_integer_certificates
#print axioms all_generalized_certificates
#print axioms generalized_nonzero
end JSP404.Regression
