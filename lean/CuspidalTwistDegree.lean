import CuspidalTwistBaseChange

/-! Descent respects the map to the parameter line, including the exact
function-field degree before and after extending the constants. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral FiniteDimensional
open scoped TensorProduct
noncomputable section
variable {F : Type*} [Field F] [Fintype F] {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
  (S : Finset F) (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

scoped instance rationalConstantAlgebra (F : Type*) [Field F] :
    Algebra (RatFunc F) (RatFunc (AlgebraicClosure F)) := (parameterInclusion F).toAlgebra

def geometricParameterMap (d : ℕ) (a : F) (S : Finset F) :
    RatFunc (AlgebraicClosure F) →ₐ[RatFunc F] GeometricSplitting d a S :=
  IsScalarTower.toAlgHom (RatFunc F) (RatFunc (AlgebraicClosure F)) _

def fixedParameterMap (d : ℕ) (a : F) (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S) :
    twistField d a S g →ₐ[RatFunc F] GeometricSplitting d a S where
  toRingHom := (twistField d a S g).subtype
  commutes' _ := rfl

theorem twist_parameter_product_bijective : Function.Bijective
    (Algebra.TensorProduct.productMap (geometricParameterMap d a S) (fixedParameterMap d a S g)) := by
  let C := geometricParameterMap d a S
  let U := fixedParameterMap d a S g
  constructor
  · exact productMap_injective_of_frobenius (coefficientFrobenius F) (twistAut d a S g) C U
      (fun z hz => (coefficientFrobenius_fixed_iff F z).1 hz)
      (twistAut_parameter d a S g) (fun x => x.property)
  · intro x
    let m := Algebra.TensorProduct.productMap (constantInclusion d a S) (twistInclusion d a S g)
    let B := (Algebra.TensorProduct.productMap C U).range
    obtain ⟨t, rfl⟩ := (twist_constant_product_bijective hd ha S g).2 x
    change m t ∈ B
    induction t using TensorProduct.induction_on with
    | zero => rw [m.map_zero]; exact B.zero_mem
    | tmul c z => exact ⟨RatFunc.C c ⊗ₜ[RatFunc F] z,rfl⟩
    | add t u ht hu => rw [m.map_add]; exact B.add_mem ht hu

def twist_parameter_tensor_equiv :
    RatFunc (AlgebraicClosure F) ⊗[RatFunc F] (twistField d a S g) ≃ₐ[RatFunc (AlgebraicClosure F)]
      GeometricSplitting d a S :=
  AlgEquiv.ofBijective (Algebra.TensorProduct.productLeftAlgHom
    (Algebra.ofId (RatFunc (AlgebraicClosure F)) _) (fixedParameterMap d a S g))
    (twist_parameter_product_bijective hd ha S g)

theorem twist_parameter_tensor_equiv_tmul (f : RatFunc (AlgebraicClosure F)) (x : twistField d a S g) :
    twist_parameter_tensor_equiv hd ha S g (f ⊗ₜ[RatFunc F] x) =
      algebraMap (RatFunc (AlgebraicClosure F)) (GeometricSplitting d a S) f * x.val := rfl

/-- A basis over the rational parameter field extends to a basis of the
geometric cover, so even in wild characteristic the twist has the same
finite covering degree. -/
theorem twist_degree_eq :
    FiniteDimensional (RatFunc F) (twistField d a S g) ∧
      finrank (RatFunc F) (twistField d a S g) =
        finrank (RatFunc (AlgebraicClosure F)) (GeometricSplitting d a S) := by
  classical
  let b := Basis.ofVectorSpace (RatFunc F) (twistField d a S g)
  let B := (Algebra.TensorProduct.basis (RatFunc (AlgebraicClosure F)) b).map
    (twist_parameter_tensor_equiv hd ha S g).toLinearEquiv
  letI := B.fintypeIndexOfRankLtAleph0 (rank_lt_aleph0 _ _)
  exact ⟨FiniteDimensional.of_fintype_basis b,
    (finrank_eq_card_basis b).trans (finrank_eq_card_basis B).symm⟩

end
end BlockingCurves.CuspidalDescent
