import PhaseCommonVariable
import Mathlib.Algebra.GCDMonoid.Finset

namespace BlockingCurves.PiecewiseCandidates

/-- The period of the table of multipliers; repeated values do not change it. -/
noncomputable def coefficientPeriod {G : Type*} [CommGroup G]
    (C : Finset G) (base : G) : ℕ :=
  C.lcm (fun c => orderOf (c / base))

theorem coefficientPeriod_dvd_iff {G : Type*} [CommGroup G]
    (C : Finset G) (base : G) (n : ℕ) :
    coefficientPeriod C base ∣ n ↔ ∀ c ∈ C, c ^ n = base ^ n := by
  unfold coefficientPeriod
  simp only [Finset.lcm_dvd_iff, orderOf_dvd_iff_pow_eq_one, div_pow, div_eq_one]

open PhaseCommonVariable

/-- Prescribing a class outside *all* labels of the branch excludes an actual
line. The finite product uses distinct coefficients, while the table may
assign the same coefficient to many labels. The label at zero is arbitrary. -/
theorem wrong_classes_miss {F E I : Type*} [Field F] [Field E] [Algebra F E]
    [DecidableEq F] (σ : E ≃ₐ[F] E) (label : E → I) (β : I → F)
    (C : Finset F) (members : ∀ i, β i ∈ C) {a : E} (ha : a ≠ 0)
    (t : E) (S : Set E)
    (wrong : ∀ z ∈ C, ∀ α ∈ S, ∀ u : E, algebraMap F E z * σ u - a * u = α →
      let x := productEnd (normalized σ a) (C.erase z) t + u
      x ≠ 0 ∧ β (label x) ≠ z) :
    ¬GraphHits (fun x => algebraMap F E (β (label x)) * σ x) S := by
  let b := a * productEnd (normalized σ a) C t
  intro blocks
  obtain ⟨x,hx⟩ := blocks a b
  let z := β (label x)
  let α := algebraMap F E z * σ x - a * x - b
  have hz : z ∈ C := members _
  have hit : algebraMap F E z * σ x - a * x = b + α := by dsimp [α]; abel
  obtain ⟨u,hu,hxu⟩ := (candidate_iff σ ha C hz t α x).1 hit
  have hwrong := (wrong z hz α hx u hu).2
  rw [← hxu] at hwrong
  exact hwrong rfl

end BlockingCurves.PiecewiseCandidates
