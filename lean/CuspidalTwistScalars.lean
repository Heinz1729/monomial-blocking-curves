import CuspidalTwistDescent

/-! Compatible scalar maps for the actual fixed subfield and the two
constant extensions, over the constants and over the parameter line. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral
noncomputable section
variable {F : Type*} [Field F] [Fintype F]
variable (d : ℕ) (a : F) (S : Finset F)
  (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)

def twistParameter : RatFunc F →+* twistField d a S g :=
  ((algebraMap (RatFunc (AlgebraicClosure F)) _).comp (parameterInclusion F)).codRestrict
    (twistField d a S g) (twist_parameter_mem d a S g)

instance twistParameterAlgebra : Algebra (RatFunc F) (twistField d a S g) :=
  (twistParameter d a S g).toAlgebra

instance twistConstantAlgebra : Algebra F (twistField d a S g) :=
  ((twistParameter d a S g).comp RatFunc.C).toAlgebra

instance twistScalarTower : IsScalarTower F (RatFunc F) (twistField d a S g) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem twistParameter_coe (z : RatFunc F) :
    (twistParameter d a S g z : GeometricSplitting d a S) =
      algebraMap _ _ (parameterInclusion F z) := rfl

def constantInclusion : AlgebraicClosure F →ₐ[F] GeometricSplitting d a S where
  toRingHom := geomConstant d a S
  commutes' _ := rfl

theorem constantInclusion_apply (z : AlgebraicClosure F) :
    constantInclusion d a S z = geomConstant d a S z :=
  rfl

instance geometricConstantTower : IsScalarTower F (AlgebraicClosure F) (GeometricSplitting d a S) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

def twistInclusion : twistField d a S g →ₐ[F] GeometricSplitting d a S where
  toRingHom := (twistField d a S g).subtype
  commutes' c := by
    change algebraMap _ _ (parameterInclusion F (RatFunc.C c)) = _
    rw [parameterInclusion_C]
    exact ((constantInclusion_apply d a S _).symm.trans ((constantInclusion d a S).commutes c))

theorem twistInclusion_apply (x : twistField d a S g) : twistInclusion d a S g x = x.val := rfl

end
end BlockingCurves.CuspidalDescent
