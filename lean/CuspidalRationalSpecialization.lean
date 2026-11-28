import CuspidalTwistScalars
import CuspidalTwistBaseChange
import CuspidalIntegralSheets
import CuspidalTensorResidue
import CuspidalTwistSpecialization
import CubicFiniteFibres

/-! A rational place of the fixed field evaluates the sheets in the
constant extension of its valuation ring. This also treats finite places
under a ramified intercept; separability is used only for conjugacy. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral CubicRepairPlaces CubicFiniteFibres Algebra.TensorProduct
noncomputable section
universe u
variable {F : Type u} [Field F] [Fintype F]
variable {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
  (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

private def residueFrobenius (F : Type*) [Field F] [Fintype F] :
    AlgebraicClosure F →ₐ[F] AlgebraicClosure F where
  toRingHom := (exists_constantPower F 1).choose
  commutes' c := by
    simpa only [pow_one, ← map_pow, FiniteField.pow_card] using
      (exists_constantPower F 1).choose_spec (algebraMap F (AlgebraicClosure F) c)

private theorem residueFrobenius_apply (x : AlgebraicClosure F) :
    residueFrobenius F x = x ^ Fintype.card F := by
  change (exists_constantPower F 1).choose x = _
  simpa only [pow_one] using (exists_constantPower F 1).choose_spec x

private theorem local_chart_of_sheets
    (p : RationalPlace F (twistField d a S g)) {b : F} (above : fieldBasePoint p = some b)
    (injective : Function.Injective (productMap (constantInclusion d a S) (twistInclusion d a S g)))
    (sheets : ∀ (B : Subring (GeometricSplitting d a S)),
        (∀ c, geomConstant d a S c ∈ B) →
        (∀ t : p.ring, ((t : twistField d a S g) : GeometricSplitting d a S) ∈ B) →
        ∀ α j, (rootLabel hd ha S α j).val ∈ B) : Nonempty (TwistReductionChart hd ha S g b) := by
  classical
  let D := twistField d a S g
  let M := GeometricSplitting d a S
  let C := constantInclusion d a S
  let U := twistInclusion d a S g
  let con := (baseConstant F D).codRestrict p.ring.toSubring p.constants
  letI : Algebra F p.ring := con.toAlgebra
  let i : p.ring →ₐ[F] D := { toRingHom := p.ring.subtype, commutes' := fun _ => rfl }
  let v : p.ring →ₐ[F] F := { toRingHom := p.residue, commutes' := p.on_constants }
  have hi : Function.Injective i := Subtype.val_injective
  let B := chartRing C U i
  have cmem (c) : geomConstant d a S c ∈ B := constantInclusion_apply d a S c ▸ constant_mem_chart C U i c
  have omem (x : p.ring) : ((x : D) : M) ∈ B := local_mem_chart C U i x
  let t := algebraMap (RatFunc F) D RatFunc.X
  have ht : t ∈ p.ring := by
    by_contra h
    simp [fieldBasePoint, show algebraMap (RatFunc F) D RatFunc.X ∉ p.ring from h] at above
  let x : p.ring := ⟨t,ht⟩
  have val : p.residue x = b := by simpa [fieldBasePoint,ht,t,x] using above
  let cn := (geomConstant d a S).codRestrict B cmem
  refine ⟨{ ring := B, constants := cn, constants_lift := fun _ => rfl
            parameter := ⟨U (i x),omem x⟩, parameter_lift := ?_
            residue := chartResidue C U i injective hi v
            on_constants := ?_, at_parameter := ?_, sheet_mem := sheets B cmem omem
            equivariant := ?_ }⟩
  · change algebraMap (RatFunc (AlgebraicClosure F)) M (parameterInclusion F RatFunc.X) = _
    rw [parameterInclusion_X]
  · intro c
    have e : cn c = (⟨C c,constant_mem_chart C U i c⟩ : B) :=
      Subtype.ext (constantInclusion_apply d a S c).symm
    rw [e]
    exact chartResidue_constant C U i injective hi v c
  · exact (chartResidue_local C U i injective hi v x).trans (congrArg (algebraMap F _) val)
  · intro y z hz
    rw [←residueFrobenius_apply]
    apply chartResidue_equivariant C U i injective hi v (twistAut d a S g) (residueFrobenius F) _ _ y z hz
    · intro c
      simp only [C,constantInclusion_apply,twistAut_constant,residueFrobenius_apply]
    · exact fun t => t.property

/-- Evaluation at an actual rational place uses all the integral sheets.
The only algebraic input to this construction is faithfulness of the
canonical multiplication map for the constant extension. -/
theorem rational_place_conjugacy_of_injective [DecidableEq F]
    (injective : Function.Injective (productMap (constantInclusion d a S) (twistInclusion d a S g)))
    (p : RationalPlace F (twistField d a S g)) {b : F} (above : fieldBasePoint p = some b)
    (hb : some b ∉ excludedBranches d a S) (α : S) :
    IsConj (regularFibreAction hd ha S hb α).perm
      ((frobeniusRootAction hd ha S * geometricRootAction hd ha S g) α) := by
  classical
  refine specialization_of_chart hd ha S g hb (Classical.choice ?_) α
  apply local_chart_of_sheets hd ha S g p above injective
  intro B hc ho β j
  let D := twistField d a S g
  let inc := (baseConstant F D).codRestrict p.ring.toSubring p.constants
  let t := algebraMap (RatFunc F) D RatFunc.X
  have ht : t ∈ p.ring := by
    by_contra h
    simp [fieldBasePoint, show algebraMap (RatFunc F) D RatFunc.X ∉ p.ring from h] at above
  apply sheets_mem_local_chart hd ha S g p.ring inc _ (⟨t,ht⟩ : p.ring) _ B hc ho β j
  · intro c
    change algebraMap _ _ (parameterInclusion F (RatFunc.C c)) = _
    rw [parameterInclusion_C]
    rfl
  · change algebraMap _ _ (parameterInclusion F RatFunc.X) = _
    rw [parameterInclusion_X]

/-- Every rational place above the regular locus realizes the specified
Frobenius conjugacy class on every coordinate of this actual twist. -/
theorem rational_place_specialization [DecidableEq F]
    (p : RationalPlace F (twistField d a S g)) {b : F}
    (above : fieldBasePoint p = some b) (hb : some b ∉ excludedBranches d a S) (α : S) :
    IsConj (regularFibreAction hd ha S hb α).perm
      ((frobeniusRootAction hd ha S * geometricRootAction hd ha S g) α) :=
  rational_place_conjugacy_of_injective hd ha S g
    (twist_constant_product_bijective hd ha S g).injective p above hb α

end
end BlockingCurves.CuspidalDescent
