import CubicRepairDegree
import CubicRepairPlaces
import CubicPoleFibre
import CubicPoleScalars

/-! Bounding a rational pole fibre by the degree using its residue maps. -/
namespace BlockingCurves.CubicPoleDegree
open Finset IntermediateField FiniteDimensional CubicAlteration CubicRepairPlaces
variable {F : Type*} [Field F] [Fintype F] {R : Finset (Line F)}

theorem branch_finite (D : Branch F R) : FiniteDimensional (RatFunc F) D.K := by
  have h := (CubicRepairDegree.generated_degree (univ : Finset R) D.root
    (fun i => RatFunc.C (i.val.1:F)) (fun i => RatFunc.X + RatFunc.C i.val.2)
    (fun i _ => D.equation i)).1
  rw [coe_univ, Set.image_univ, D.generated] at h
  letI : FiniteDimensional (RatFunc F) (⊤ : IntermediateField (RatFunc F) D.K) := h
  exact FiniteDimensional.of_injective (IntermediateField.topEquiv.toLinearEquiv.symm : D.K ≃ₗ[RatFunc F] _)
    (IntermediateField.topEquiv (F := RatFunc F) (E := D.K)).symm.injective

/-- A relation normalized at its largest coefficient cannot vanish: at the
corresponding place only its diagonal summand has nonzero residue. -/
private theorem independent_of_residues (D : Branch F R) {I : Type*} [Fintype I] [DecidableEq I]
    (p : I → Place D) (s : I → D.K)
    (hs : ∀ i j, ∃ h : s i ∈ (p j).ring, (p j).residue ⟨s i,h⟩ = if i = j then 1 else 0)
    (normalize : ∀ a : I → RatFunc F, (∃ i, a i ≠ 0) →
      ∃ j, a j ≠ 0 ∧ ∀ i, algebraMap (RatFunc F) D.K (a i/a j) ∈ (p j).ring) :
    LinearIndependent (RatFunc F) s := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a he i
  by_contra hi
  obtain ⟨j,hj,hreg⟩ := normalize a ⟨i,hi⟩
  let O := (p j).ring
  let c (k : I) : O := ⟨algebraMap (RatFunc F) D.K (a k / a j),hreg k⟩
  let f (k : I) : O := ⟨s k,(hs k j).choose⟩
  have zeroSum : ∑ k, algebraMap (RatFunc F) D.K (a k/a j)*s k = 0 := calc
    _ = ∑ k, (algebraMap (RatFunc F) D.K (a j))⁻¹ * (a k • s k) := by
      apply sum_congr rfl
      intro k _
      rw [map_div₀, Algebra.smul_def, div_eq_mul_inv]
      ring
    _ = 0 := by rw [← mul_sum, he, mul_zero]
  have hz : ∑ k, c k * f k = 0 := by
    apply Subtype.ext
    change O.toSubring.subtype (∑ k, c k*f k) = O.toSubring.subtype 0
    simpa only [map_sum, map_mul, map_zero] using zeroSum
  have diag : c j = 1 := by
    apply Subtype.ext
    change algebraMap (RatFunc F) D.K (a j/a j) = 1
    simp [hj]
  have val (k : I) : (p j).residue (f k) = if k = j then 1 else 0 := (hs k j).choose_spec
  have hr := congrArg (p j).residue hz
  simp only [map_sum, map_mul, map_zero, val] at hr
  simp [mul_ite, diag] at hr

/-- Distinct rational places over the pole of the base parameter are bounded
by the actual extension degree, even in wild characteristic. -/
theorem card_le_degree_of_polar (D : Branch F R) (P : Finset (Place D))
    (polar : ∀ p ∈ P, parameter D ∉ p.ring) : P.card ≤ finrank (RatFunc F) D.K := by
  classical
  obtain ⟨s,hs⟩ := CubicPoleFibre.selectors P
  have independent : LinearIndependent (RatFunc F) s := by
    apply independent_of_residues D (fun j : P => j.val) s hs
    intro a ha
    obtain ⟨j,hj,hreg⟩ := CubicPoleScalars.normalize D a ha
    exact ⟨j,hj,hreg j.val (polar j.val j.property)⟩
  letI := branch_finite D
  simpa only [Fintype.card_coe] using independent.fintype_card_le_finrank

end BlockingCurves.CubicPoleDegree
