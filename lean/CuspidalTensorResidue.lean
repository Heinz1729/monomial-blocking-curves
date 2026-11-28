import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Residue evaluation after extending constants in a rational place. The
chart is the image of the constant extension of its valuation ring. -/
namespace BlockingCurves.CuspidalDescent
open scoped TensorProduct
open Algebra.TensorProduct
noncomputable section
variable {F k D M R : Type*} [Field F] [Field k] [Field D] [Field M] [CommRing R]
  [Algebra F k] [Algebra F D] [Algebra F M] [Algebra F R]
  (C : k →ₐ[F] M) (U : D →ₐ[F] M) (i : R →ₐ[F] D)

private theorem tensorChart_injective
    (h : Function.Injective (productMap C U)) (hi : Function.Injective i) :
    Function.Injective (productMap C (U.comp i)) := by
  obtain ⟨j,hj⟩ := i.toLinearMap.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  let f := Algebra.TensorProduct.map (AlgHom.id F k) i
  have left (x : k ⊗[F] R) : j.lTensor k (f x) = x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [show f (a ⊗ₜ[F] b) = a ⊗ₜ[F] i b from rfl, LinearMap.lTensor_tmul]
      exact congrArg (fun t => a ⊗ₜ[F] t) (LinearMap.congr_fun hj b)
    | add x y hx hy => simp only [map_add,hx,hy]
  have comp (x : k ⊗[F] R) : productMap C (U.comp i) x = productMap C U (f x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  intro x y eqn
  rw [comp,comp] at eqn
  exact (left x).symm.trans ((congrArg (j.lTensor k) (h eqn)).trans (left y))

abbrev chartMap := productMap C (U.comp i)
abbrev chartRing := (chartMap C U i).toRingHom.range

variable (h : Function.Injective (productMap C U)) (hi : Function.Injective i) (v : R →ₐ[F] F)

private def chartEquiv : (k ⊗[F] R) ≃+* chartRing C U i :=
  RingEquiv.ofLeftInverse (f := (chartMap C U i).toRingHom)
    (Function.leftInverse_invFun (tensorChart_injective C U i h hi))

def chartResidue : chartRing C U i →+* k :=
  (productMap (AlgHom.id F k) ((Algebra.ofId F k).comp v)).toRingHom.comp
    (chartEquiv C U i h hi).symm.toRingHom

theorem chartResidue_apply (x : k ⊗[F] R) :
    chartResidue C U i h hi v ⟨chartMap C U i x, x, rfl⟩ =
    productMap (AlgHom.id F k) ((Algebra.ofId F k).comp v) x := by
  exact congrArg (productMap (AlgHom.id F k) ((Algebra.ofId F k).comp v))
    ((chartEquiv C U i h hi).symm_apply_apply x)

theorem constant_mem_chart (c : k) : C c ∈ chartRing C U i :=
  ⟨c ⊗ₜ[F] 1, productMap_left_apply _ _ _⟩

theorem local_mem_chart (x : R) : U (i x) ∈ chartRing C U i :=
  ⟨1 ⊗ₜ[F] x, productMap_right_apply _ _ _⟩

theorem chartResidue_constant (c : k) :
    chartResidue C U i h hi v ⟨C c,constant_mem_chart C U i c⟩ = c := by
  have eqn : (⟨C c,constant_mem_chart C U i c⟩ : chartRing C U i) =
    ⟨chartMap C U i (c ⊗ₜ[F] 1), _, rfl⟩ := Subtype.ext (productMap_left_apply _ _ _).symm
  rw [eqn, chartResidue_apply, productMap_left_apply]
  rfl

theorem chartResidue_local (x : R) :
    chartResidue C U i h hi v ⟨U (i x),local_mem_chart C U i x⟩ = algebraMap F k (v x) := by
  have eqn : (⟨U (i x),local_mem_chart C U i x⟩ : chartRing C U i) =
    ⟨chartMap C U i (1 ⊗ₜ[F] x), _, rfl⟩ := Subtype.ext (productMap_right_apply C (U.comp i) x).symm
  rw [eqn, chartResidue_apply, productMap_right_apply]
  rfl

/-- A semilinear automorphism fixing D acts coefficientwise on the entire
chart and on its residue, even if some special sheets coalesce. -/
theorem chartResidue_equivariant (τ : M ≃+* M) (f : k →ₐ[F] k)
    (hc : ∀ c, τ (C c) = C (f c)) (hu : ∀ t, τ (U t) = U t)
    (x y : chartRing C U i) (eqn : (y : M) = τ x) :
    chartResidue C U i h hi v y = f (chartResidue C U i h hi v x) := by
  let lift := Algebra.TensorProduct.map f (AlgHom.id F R)
  let red := productMap (AlgHom.id F k) ((Algebra.ofId F k).comp v)
  have map_chart (t : k ⊗[F] R) : chartMap C U i (lift t) = τ (chartMap C U i t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => change C (f a) * U (i b) = τ (C a * U (i b)); rw [map_mul,hc,hu]
    | add x y hx hy => simp only [map_add,hx,hy]
  have map_red (t : k ⊗[F] R) : red (lift t) = f (red t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      change f a * algebraMap F k (v b) = f (a * algebraMap F k (v b))
      rw [map_mul, f.commutes]
    | add x y hx hy => simp only [map_add,hx,hy]
  obtain ⟨s,hs⟩ := x.property
  have xeq : x = ⟨chartMap C U i s,s,rfl⟩ := Subtype.ext hs.symm
  have yeq : y = ⟨chartMap C U i (lift s),lift s,rfl⟩ :=
    Subtype.ext (eqn.trans ((congrArg τ hs).symm.trans (map_chart s).symm))
  rw [xeq,yeq,chartResidue_apply,chartResidue_apply]
  exact map_red s

end
end BlockingCurves.CuspidalDescent
