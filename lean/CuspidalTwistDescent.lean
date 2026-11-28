import CuspidalGeometricFrobenius
import CuspidalOrbitDescent
import CuspidalPeriodicConstants
import CuspidalParameterDescent
import CubicRepairPlaces

/-! The twist is the fixed subfield of an actual semilinear lift in the
geometric product splitting field. Constant extension recovers every sheet. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral Polynomial Function
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

variable (d : ℕ) (a : F) (S : Finset F)
  (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

def twistAut : GeometricSplitting d a S ≃+* GeometricSplitting d a S :=
  g.toRingEquiv.trans (geometricFrobenius d a S)

def twistField : Subfield (GeometricSplitting d a S) := fixedField (twistAut d a S g)

def geomConstant : AlgebraicClosure F →+* GeometricSplitting d a S :=
  (algebraMap (RatFunc (AlgebraicClosure F)) _).comp RatFunc.C

theorem twistAut_parameter (z : RatFunc (AlgebraicClosure F)) :
    twistAut d a S g (algebraMap _ _ z) = algebraMap _ _ (coefficientFrobenius F z) := by
  change geometricFrobenius d a S (g (algebraMap _ _ z)) = _
  rw [g.commutes, geometricFrobenius_extends]

theorem twistAut_constant (z : AlgebraicClosure F) :
    twistAut d a S g (geomConstant d a S z) = geomConstant d a S (z ^ Fintype.card F) := by
  simpa only [geomConstant, RingHom.comp_apply, coefficientFrobenius_C] using
    twistAut_parameter d a S g (RatFunc.C z)

theorem iterate_constant (z : AlgebraicClosure F) (n : ℕ) :
    (twistAut d a S g : _ → _)^[n] (geomConstant d a S z) =
      geomConstant d a S (z ^ (Fintype.card F)^n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply', ih, twistAut_constant, ←pow_mul, pow_succ]

theorem twist_parameter_mem (z : RatFunc F) :
    algebraMap _ (GeometricSplitting d a S) (parameterInclusion F z) ∈ twistField d a S g := by
  change twistAut d a S g _ = _
  rw [twistAut_parameter, (coefficientFrobenius_fixed_iff F _).2 ⟨z,rfl⟩]
  rfl

/-- An arbitrary rational function belongs to any subfield containing its
constant coefficients and the parameter. -/
theorem rational_range_le {k M : Type*} [Field k] [Field M]
    (f : RatFunc k →+* M) (L : Subfield M)
    (constants : ∀ c, f (RatFunc.C c) ∈ L) (parameter : f RatFunc.X ∈ L) :
    ∀ z, f z ∈ L := CubicRepairPlaces.map_ratfunc_mem f L constants parameter

theorem twist_baseChange_top {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S) :
    twistField d a S g ⊔ (geomConstant d a S).fieldRange = ⊤ := by
  classical
  let k := AlgebraicClosure F
  let M := GeometricSplitting d a S
  let ι := algebraMap (RatFunc k) M
  let L := twistField d a S g ⊔ (geomConstant d a S).fieldRange
  have base : ∀ z, ι z ∈ L := by
    apply rational_range_le
    · exact fun c => le_sup_right (b := (geomConstant d a S).fieldRange) (RingHom.mem_fieldRange.mpr ⟨c,rfl⟩)
    · apply le_sup_left (a := twistField d a S g)
      simpa only [parameterInclusion_X] using twist_parameter_mem d a S g RatFunc.X
  let W := L.toIntermediateField base
  let P := ∏ u ∈ geometricShifts S, cuspCoordinate d (algebraMap F k a) u
  have hn : P ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun u _ => (cuspCoordinate_irreducible (by omega) _ u).ne_zero)
  have gen : IntermediateField.adjoin (RatFunc k) (P.rootSet M) = ⊤ :=
    (isSplittingField_iff_intermediateField.mp (inferInstance : P.IsSplittingField (RatFunc k) M)).2
  obtain ⟨θ,period,distinct⟩ := exists_periodic_constant F d.factorial (Nat.factorial_pos _)
  let z := geomConstant d a S θ
  let τ := twistAut d a S g
  have hz : IsPeriodicPt τ d.factorial z :=
    (iterate_constant d a S g θ _).trans (congrArg (geomConstant d a S) period)
  have inj : Function.Injective (fun i : Fin d.factorial => (τ : M → M)^[i.val] z) := by
    intro i j eqn
    apply distinct
    apply (geomConstant d a S).injective
    exact (iterate_constant d a S g θ i.val).symm.trans (eqn.trans (iterate_constant d a S g θ j.val))
  have all : ⊤ ≤ W := by
    rw [←gen]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [show P.rootSet M = _ from rootSet_prod _ (geometricShifts S) hn] at hx
    obtain ⟨v,hv,hx⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
    let i : S := ⟨w,hw⟩
    let y := (rootLabel hd ha S i).symm ⟨x,hx⟩
    have sheet : (rootLabel hd ha S i y).val = x :=
      congrArg Subtype.val ((rootLabel hd ha S i).apply_symm_apply ⟨x,hx⟩)
    have fixed : IsPeriodicPt τ d.factorial x := by
      rw [←sheet]
      exact frobenius_iterate_fixes_sheets hd ha S g i y
    exact periodic_mem_of_marker τ (Nat.factorial_pos _) hz fixed inj L le_sup_left
      (le_sup_right (b := (geomConstant d a S).fieldRange) ⟨θ,rfl⟩)
  exact eq_top_iff.mpr fun x _ => all (show x ∈ (⊤ : IntermediateField (RatFunc k) M) from trivial)

end
end BlockingCurves.CuspidalDescent
