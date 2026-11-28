import CuspidalTwistBaseChange
import CuspidalRootGenus
import Mathlib.Algebra.Field.Equiv

/-! Constants of the Frobenius-fixed function field and regular
differentials on its geometric base change. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral Polynomial
open scoped TensorProduct
noncomputable section

private theorem geometric_constant_of_integral {F k M : Type*}
    [Field F] [Field k] [Field M] [IsAlgClosed k] (f : F →+* k) (ι : k →+* M)
    {x : M} (hx : (ι.comp f).IsIntegralElem x) : ∃ c : k, ι c = x := by
  classical
  obtain ⟨P,hm,he⟩ := hx
  have h : x ∈ ((P.map f).map ι).roots := by
    apply (mem_roots (((hm.map f).map ι).ne_zero)).mpr
    simpa only [Polynomial.map_map, IsRoot.def, eval_map] using he
  rw [roots_map ι (IsAlgClosed.splits (P.map f))] at h
  obtain ⟨c,_,hc⟩ := Multiset.mem_map.mp h
  exact ⟨c,hc⟩

variable {F : Type*} [Field F] [Fintype F] (d : ℕ) (a : F) (S : Finset F)
  (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

/-- Every algebraic constant of the descended field belongs to F. The
geometric splitting field may have been formed over an infinite closure. -/
private theorem fixed_constant_iff (x : twistField d a S g) :
    let f := (geomConstant d a S).comp (algebraMap F (AlgebraicClosure F))
    f.IsIntegralElem x.val ↔ ∃ c : F, f c = x.val := by
  let f := algebraMap F (AlgebraicClosure F)
  let ι := geomConstant d a S
  constructor
  · intro hx
    obtain ⟨z,hz⟩ := geometric_constant_of_integral f ι hx
    have fixed : twistAut d a S g (ι z) = ι z := hz ▸ x.property
    have qfixed : z ^ Fintype.card F = z :=
      ι.injective ((twistAut_constant d a S g z).symm.trans fixed)
    obtain ⟨c,hc⟩ := (pow_card_eq_iff_scalar F (AlgebraicClosure F) _).mp qfixed
    exact ⟨c,(congrArg ι hc).trans hz⟩
  · rintro ⟨c,hc⟩
    refine ⟨X - C c,monic_X_sub_C _,?_⟩
    simpa only [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero] using hc.symm

/-- The full algebraic constant field of the descended model is precisely
the given finite field, under its actual structure map. -/
theorem twist_exact_constants (x : twistField d a S g) :
    IsIntegral F x ↔ ∃ c : F, algebraMap F (twistField d a S g) c = x := by
  let D := twistField d a S g
  let f := (geomConstant d a S).comp (algebraMap F (AlgebraicClosure F))
  have comp : D.subtype.comp (algebraMap F D) = f := by
    apply RingHom.ext
    intro c
    change algebraMap _ _ (parameterInclusion F (RatFunc.C c)) = _
    rw [parameterInclusion_C]
    rfl
  constructor
  · rintro ⟨P,hm,h⟩
    have root : f.IsIntegralElem x.val := by
      refine ⟨P,hm,?_⟩
      rw [←comp]
      change P.eval₂ (D.subtype.comp (algebraMap F D)) (D.subtype x) = 0
      rw [← hom_eval₂,h,map_zero]
    obtain ⟨c,hc⟩ := (fixed_constant_iff d a S g x).mp root
    exact ⟨c, Subtype.ext ((RingHom.congr_fun comp c).trans hc)⟩
  · rintro ⟨c,rfl⟩
    exact isIntegral_algebraMap

section Geometry
variable {d a}
local notation "k" => AlgebraicClosure F
local notation "M" => GeometricSplitting d a S
local notation "T" => k ⊗[F] twistField d a S g

private def fieldOfAlgEquiv {R A B : Type*} [Field R] [CommRing A] [Field B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) : Field A :=
  (MulEquiv.isField B (Field.toIsField B) e.toRingEquiv.toMulEquiv).toField

/-- The constant extension is itself a field, with its original tensor
product addition and multiplication. -/
def twistTensorField (hd : 3 ≤ d) (ha : a ≠ 0) : Field T := by
  exact fieldOfAlgEquiv (R := k) (A := T) (B := M) (twist_constant_tensor_equiv hd ha S g)

/-- Geometric genus of the fixed function field, measured on its actual
tensor product with the algebraic closure of the finite constant field. -/
def twistGeometricGenus (hd : 3 ≤ d) (ha : a ≠ 0) : ℕ :=
  letI := twistTensorField S g hd ha
  CubicRationalGenus.genus k T

/-- Under geometric base change, the isomorphism of function fields
identifies regular differentials on all normal affine charts. -/
def twist_geometric_regularForms (hd : 3 ≤ d) (ha : a ≠ 0) :
    letI := twistTensorField S g hd ha
    letI : Algebra k M := (geomConstant d a S).toAlgebra
    CubicRationalGenus.regularForms k T ≃ₗ[k] CubicRationalGenus.regularForms k M := by
  letI := twistTensorField S g hd ha
  let e := (twist_constant_tensor_equiv hd ha S g).toRingEquiv
  have constants (c : k) : e (algebraMap k T c) = geomConstant d a S c := by
    change twist_constant_tensor_equiv hd ha S g (c ⊗ₜ[F] (1 : twistField d a S g)) = _
    rw [twist_constant_tensor_equiv_tmul]
    exact mul_one _
  letI : Algebra k M := (geomConstant d a S).toAlgebra
  exact CubicRationalGenus.regularFormsEquiv (AlgEquiv.ofRingEquiv (f := e) constants)

theorem twist_geometric_genus (hd : 3 ≤ d) (ha : a ≠ 0) :
    twistGeometricGenus S g hd ha = CuspidalTower.ambientGenus k M := by
  letI := twistTensorField S g hd ha
  exact (twist_geometric_regularForms S g hd ha).finrank_eq

end Geometry

end
end BlockingCurves.CuspidalDescent
