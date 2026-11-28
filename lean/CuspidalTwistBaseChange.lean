import CuspidalTwistScalars
import CuspidalTensorDescent

/-! Constant extension of the descended twist, as a tensor-product
isomorphism respecting the actual embeddings of both factors. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral
open scoped TensorProduct
noncomputable section
variable {F : Type*} [Field F] [Fintype F] {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
  (S : Finset F) (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

private theorem constantFrob_exists (F : Type*) [Field F] [Fintype F] :
    ∃ κ : AlgebraicClosure F ≃+* AlgebraicClosure F, ∀ c, κ c = c ^ Fintype.card F := by
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  let K := AlgebraicClosure F
  letI : CharP K (ringChar F) := charP_of_injective_algebraMap' F K _
  letI : ExpChar K (ringChar F) := ExpChar.prime hp
  refine ⟨iterateFrobeniusEquiv K (ringChar F) n, fun c => ?_⟩
  change c ^ (ringChar F)^(n:ℕ) = _
  rw [←hn]

theorem twist_constant_product_bijective : Function.Bijective
    (Algebra.TensorProduct.productMap (constantInclusion d a S) (twistInclusion d a S g)) := by
  let C := constantInclusion d a S
  let U := twistInclusion d a S g
  constructor
  · obtain ⟨κ,pow⟩ := constantFrob_exists F
    exact productMap_injective_of_frobenius κ (twistAut d a S g) C U
      (fun c hc => (pow_card_eq_iff_scalar F (AlgebraicClosure F) c).mp ((pow c).symm.trans hc))
      (fun c => (twistAut_constant d a S g c).trans (congrArg C (pow c).symm))
      (fun x => x.property)
  · intro x
    letI : Algebra.IsAlgebraic F C.fieldRange := ⟨fun y => by
      apply IntermediateField.isAlgebraic_iff.mpr
      obtain ⟨c,hc⟩ := y.property
      rw [←hc]
      exact (Algebra.IsAlgebraic.isAlgebraic (R := F) c).algHom C⟩
    let L := C.fieldRange ⊔ U.fieldRange
    have contains : twistField d a S g ⊔ (geomConstant d a S).fieldRange ≤ L.toSubfield :=
      sup_le (fun y hy => (le_sup_right : U.fieldRange ≤ L) (show y ∈ U.fieldRange from ⟨⟨y,hy⟩,rfl⟩))
        (fun _ hy => (le_sup_left : C.fieldRange ≤ L) hy)
    have hx : x ∈ L.toSubfield := contains ((twist_baseChange_top hd ha S g).symm ▸ trivial)
    change x ∈ (Algebra.TensorProduct.productMap C U).range
    rw [Algebra.TensorProduct.productMap_range]
    change x ∈ C.fieldRange.toSubalgebra ⊔ U.fieldRange.toSubalgebra
    rw [←IntermediateField.sup_toSubalgebra_of_isAlgebraic_left]
    exact hx

def twist_constant_tensor_equiv :
    AlgebraicClosure F ⊗[F] (twistField d a S g) ≃ₐ[AlgebraicClosure F] GeometricSplitting d a S :=
  AlgEquiv.ofBijective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId (AlgebraicClosure F) (GeometricSplitting d a S)) (twistInclusion d a S g))
    (twist_constant_product_bijective hd ha S g)

theorem twist_constant_tensor_equiv_tmul (c : AlgebraicClosure F) (x : twistField d a S g) :
    twist_constant_tensor_equiv hd ha S g (c ⊗ₜ[F] x) = geomConstant d a S c * x.val := rfl

end
end BlockingCurves.CuspidalDescent
