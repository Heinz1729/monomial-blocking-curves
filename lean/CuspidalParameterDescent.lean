import CuspidalGeometricFrobenius

/-! The fixed field on the intercept line. Fixing a rational function fixes
its reduced numerator and monic denominator coefficient by coefficient. -/
namespace BlockingCurves.CuspidalDescent
open CuspidalGeneral Polynomial
noncomputable section
variable (F : Type*) [Field F]

private abbrev inc := algebraMap F (AlgebraicClosure F)

def parameterInclusion : RatFunc F →+* RatFunc (AlgebraicClosure F) :=
  let p := (algebraMap (AlgebraicClosure F)[X] (RatFunc (AlgebraicClosure F))).comp (mapRingHom (inc F))
  RatFunc.liftRingHom p (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    ((IsFractionRing.injective _ _).comp (map_injective (inc F) (inc F).injective)))

theorem parameterInclusion_poly (P : F[X]) :
    parameterInclusion F (algebraMap F[X] (RatFunc F) P) =
      algebraMap _ (RatFunc (AlgebraicClosure F)) (P.map (inc F)) := by
  simp [parameterInclusion, RatFunc.liftRingHom_apply]

theorem parameterInclusion_C (c : F) :
    parameterInclusion F (RatFunc.C c) = RatFunc.C (inc F c) := by
  simpa only [RatFunc.algebraMap_C, map_C] using parameterInclusion_poly F (C c)

theorem parameterInclusion_X : parameterInclusion F RatFunc.X = RatFunc.X := by
  simpa only [RatFunc.algebraMap_X, map_X] using parameterInclusion_poly F X

variable [Fintype F]

private theorem fixed_reduced {k : Type*} [Field k] (e : RatFunc k ≃+* RatFunc k)
    (f : k →+* k) (pol : ∀ p : k[X], e (algebraMap _ _ p) = algebraMap _ _ (p.map f))
    (z : RatFunc k) (hz : e z = z) : z.num.map f = z.num ∧ z.denom.map f = z.denom := by
  have rep := congrArg e (RatFunc.num_div_denom z)
  rw [map_div₀, pol, pol, hz] at rep
  have dvd := RatFunc.denom_div_dvd (z.num.map f) (z.denom.map f)
  rw [rep] at dvd
  have hd := eq_of_monic_of_dvd_of_natDegree_le (RatFunc.monic_denom z)
    ((RatFunc.monic_denom z).map f) dvd (natDegree_map_le _ _)
  have h := (RatFunc.num_mul_eq_mul_denom_iff ((RatFunc.monic_denom z).map f).ne_zero).2 rep.symm
  rw [hd] at h
  exact ⟨(mul_right_cancel₀ (RatFunc.denom_ne_zero z) h).symm, hd⟩

/-- A coefficientwise Frobenius-fixed rational function comes from the
original parameter line, including fractions with nonconstant denominator. -/
theorem coefficientFrobenius_fixed_iff (z : RatFunc (AlgebraicClosure F)) :
    coefficientFrobenius F z = z ↔ ∃ u, parameterInclusion F u = z := by
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  let k := AlgebraicClosure F
  letI : CharP k (ringChar F) := charP_of_injective_algebraMap' F k _
  letI : ExpChar k (ringChar F) := ExpChar.prime hp
  let f := iterateFrobenius k (ringChar F) n
  have hf (c : k) : f c = c ^ Fintype.card F := by
    change c ^ (ringChar F)^(n : ℕ) = _
    rw [←hn]
  have pol (p : k[X]) : coefficientFrobenius F (algebraMap k[X] _ p) =
      algebraMap k[X] (RatFunc k) (p.map f) := by
    induction p using Polynomial.induction_on' with
    | h_add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
    | h_monomial n c =>
      simp only [← C_mul_X_pow_eq_monomial, map_mul, map_pow, Polynomial.map_mul,
        Polynomial.map_pow, map_C, map_X, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
        coefficientFrobenius_C, coefficientFrobenius_X, hf]
      rw [coefficientFrobenius_C F c, coefficientFrobenius_X F, map_pow]
  have descend (p : k[X]) (h : p.map f = p) : ∃ t : F[X], t.map (inc F) = p := by
    apply (mem_map_range (inc F)).2
    intro i
    have eqn := congrArg (fun t : k[X] => t.coeff i) h
    change (p.map f).coeff i = p.coeff i at eqn
    rw [coeff_map, hf] at eqn
    exact (pow_card_eq_iff_scalar F k _).mp eqn
  constructor
  · intro hz
    obtain ⟨hN,hD⟩ := fixed_reduced _ f pol z hz
    obtain ⟨N,hN⟩ := descend _ hN
    obtain ⟨D,hD⟩ := descend _ hD
    refine ⟨algebraMap F[X] (RatFunc F) N / algebraMap F[X] (RatFunc F) D,?_⟩
    rw [map_div₀, parameterInclusion_poly, parameterInclusion_poly, hN, hD, RatFunc.num_div_denom]
  · rintro ⟨u,rfl⟩
    have fix (p : F[X]) : (p.map (inc F)).map f = p.map (inc F) := by
      ext i
      simp only [coeff_map,hf,← map_pow,FiniteField.pow_card]
    conv_lhs => rw [← RatFunc.num_div_denom u]
    rw [map_div₀, parameterInclusion_poly, parameterInclusion_poly, map_div₀, pol, pol, fix, fix,
      ←parameterInclusion_poly, ←parameterInclusion_poly, ←map_div₀, RatFunc.num_div_denom]

end
end BlockingCurves.CuspidalDescent
