import Problem
import Mathlib.Tactic

namespace JSP404

/-- The lower-and-approximate-upper specification really determines the
supremum of unavoidable angles; it does not assume that an extremizer exists. -/
theorem exactValue_isLUB {n : ℕ} {a : ℝ} (h : ExactValue n a) :
    IsLUB {b : ℝ | Unavoidable n b} a := by
  constructor
  · intro b hb
    by_contra hba
    have hab : a < b := lt_of_not_ge hba
    obtain ⟨p, hp, hc⟩ := h.2 ((b - a) / 2) (by linarith)
    obtain ⟨i, j, k, hij, hjk, hik, hbig⟩ := hb p hp
    have hsmall := hc i j k hij hjk hik
    linarith
  · intro b hb
    exact hb h.1

/-- A lower bound survives adding points. -/
theorem unavoidable_mono {m n : ℕ} {a : ℝ} (hmn : m ≤ n)
    (h : Unavoidable m a) : Unavoidable n a := by
  intro p hp
  let e : Fin m → Fin n := Fin.castLE hmn
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) hij)
  obtain ⟨i, j, k, hij, hjk, hik, ha⟩ := h (p ∘ e) (hp.comp he)
  exact ⟨e i, e j, e k, fun h ↦ hij (he h), fun h ↦ hjk (he h),
    fun h ↦ hik (he h), ha⟩

/-- Upper constructions survive discarding points. -/
theorem approximableCap_mono {m n : ℕ} {a : ℝ} (hmn : m ≤ n)
    (h : ApproximableCap n a) : ApproximableCap m a := by
  intro ε hε
  obtain ⟨p, hp, hc⟩ := h ε hε
  let e : Fin m → Fin n := Fin.castLE hmn
  have he : Function.Injective e := by
    intro i j hij
    exact Fin.ext (congrArg (fun x : Fin n ↦ x.val) hij)
  refine ⟨p ∘ e, hp.comp he, ?_⟩
  intro i j k hij hjk hik
  exact hc (e i) (e j) (e k) (fun h ↦ hij (he h))
    (fun h ↦ hjk (he h)) (fun h ↦ hik (he h))

/-- A checked assembly reduction, explicitly conditional on the unsolved
threshold families and on all upper constructions. This is NOT a proof of
FullClassification: neither hypothesis is supplied by this project. -/
theorem classification_of_thresholds
    (h3 : ExactValue 3 (Real.pi / 3))
    (h4 : ExactValue 4 (Real.pi / 2))
    (hLower : ThresholdLowerBounds)
    (hUpperFirst : ∀ m : ℕ, 2 ≤ m →
      ApproximableCap (transition m) (firstValue m))
    (hUpperSecond : ∀ m : ℕ, 2 ≤ m →
      ApproximableCap (2 ^ (m + 1)) (secondValue m)) :
    FullClassification := by
  refine ⟨h3, h4, ?_, ?_⟩
  · intro m hm n hn hn'
    exact ⟨unavoidable_mono (by omega) (hLower.1 m hm),
      approximableCap_mono hn' (hUpperFirst m hm)⟩
  · intro m hm n hn hn'
    exact ⟨unavoidable_mono (by omega) (hLower.2 m hm),
      approximableCap_mono hn' (hUpperSecond m hm)⟩

#print axioms unavoidable_mono
#print axioms approximableCap_mono
#print axioms exactValue_isLUB
#print axioms classification_of_thresholds
end JSP404
