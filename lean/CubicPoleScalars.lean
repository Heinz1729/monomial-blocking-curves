import CubicRepairPlaces
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.Algebra.Polynomial.EraseLead

/-! At a pole of the rational parameter, a nonzero polynomial has the
value of its leading monomial. Thus choosing the coefficient of greatest
rational-function degree normalizes a relation at every pole at once. -/
namespace BlockingCurves.CubicPoleScalars
open CubicAlteration CubicRepairPlaces Polynomial
universe u v
variable {F : Type u} [Field F]

private noncomputable def polyMap (K : Type v) [Field K] [Algebra (RatFunc F) K] : F[X] →+* K :=
  (algebraMap (RatFunc F) K).comp (algebraMap F[X] (RatFunc F))

private theorem constant_value (K : Type v) [Field K] [Algebra (RatFunc F) K] (p : RationalPlace F K) {c : F} (hc : c ≠ 0) :
    p.ring.valuation (baseConstant F K c) = 1 := by
  let f : F →+* p.ring := (baseConstant F K).codRestrict p.ring.toSubring p.constants
  exact (p.ring.valuation_eq_one_iff (f c)).mp ((isUnit_iff_ne_zero.mpr hc).map f)

private theorem polynomial_value (K : Type v) [Field K] [Algebra (RatFunc F) K] (p : RationalPlace F K) (hp : algebraMap (RatFunc F) K RatFunc.X ∉ p.ring)
    (f : F[X]) (hf : f ≠ 0) :
    p.ring.valuation (polyMap K f) = p.ring.valuation (algebraMap (RatFunc F) K RatFunc.X) ^ f.natDegree := by
  have ht : 1 < p.ring.valuation (algebraMap (RatFunc F) K RatFunc.X) :=
    lt_of_not_ge (fun h => hp (p.ring.mem_of_valuation_le_one _ h))
  have mon : p.ring.valuation (polyMap K (C f.leadingCoeff * X ^ f.natDegree)) =
      p.ring.valuation (algebraMap (RatFunc F) K RatFunc.X) ^ f.natDegree := by
    rw [map_mul, map_pow, map_mul, map_pow]
    change p.ring.valuation (baseConstant F K f.leadingCoeff) * _ = _
    rw [constant_value K p (leadingCoeff_ne_zero.mpr hf), one_mul]
    rfl
  have smaller : p.ring.valuation (polyMap K f.eraseLead) <
      p.ring.valuation (polyMap K (C f.leadingCoeff * X ^ f.natDegree)) := by
    rw [mon]
    by_cases hz : f.eraseLead = 0
    · rw [hz,map_zero,map_zero]
      exact zero_lt_iff.mpr (pow_ne_zero _ (zero_lt_iff.mp (zero_lt_one.trans ht)))
    · have hlt := (eraseLead_natDegree_lt_or_eraseLead_eq_zero f).resolve_right hz
      rw [polynomial_value K p hp f.eraseLead hz]
      exact pow_lt_pow_right₀ ht hlt
  calc
    _ = p.ring.valuation (polyMap K f.eraseLead +
        polyMap K (C f.leadingCoeff * X ^ f.natDegree)) := by
      rw [← map_add, eraseLead_add_C_mul_X_pow]
    _ = _ := (p.ring.valuation.map_add_eq_of_lt_right smaller).trans mon
termination_by f.natDegree

/-- Every scalar of nonpositive degree is regular at each pole of the parameter. -/
theorem regular_scalar_of_degree_nonpos (K : Type v) [Field K] [Algebra (RatFunc F) K] (p : RationalPlace F K) (hp : algebraMap (RatFunc F) K RatFunc.X ∉ p.ring)
    (a : RatFunc F) (ha : a.intDegree ≤ 0) : algebraMap (RatFunc F) K a ∈ p.ring := by
  by_cases hz : a = 0
  · simpa [hz] using p.ring.zero_mem
  have hdeg : a.num.natDegree ≤ a.denom.natDegree := by
    unfold RatFunc.intDegree at ha
    omega
  have ht : 1 < p.ring.valuation (algebraMap (RatFunc F) K RatFunc.X) :=
    lt_of_not_ge (fun h => hp (p.ring.mem_of_valuation_le_one _ h))
  apply p.ring.mem_of_valuation_le_one
  conv_lhs => rw [← RatFunc.num_div_denom a]
  rw [map_div₀, map_div₀]
  change p.ring.valuation (polyMap K a.num) / p.ring.valuation (polyMap K a.denom) ≤ 1
  rw [polynomial_value K p hp _ (RatFunc.num_ne_zero hz),
      polynomial_value K p hp _ (RatFunc.denom_ne_zero a)]
  apply (div_le_iff₀ (pow_ne_zero _ (zero_lt_iff.mp (zero_lt_one.trans ht)))).2
  simpa using pow_le_pow_right' ht.le hdeg

/-- One nonzero coefficient divides the entire family regularly at every pole.
Its own normalized value equals one, independently of the chosen place. -/
theorem normalize_field (K : Type v) [Field K] [Algebra (RatFunc F) K] {I : Type*} [Fintype I] (a : I → RatFunc F)
    (ha : ∃ i, a i ≠ 0) : ∃ j, a j ≠ 0 ∧ ∀ p : RationalPlace F K, algebraMap (RatFunc F) K RatFunc.X ∉ p.ring →
      ∀ i, algebraMap (RatFunc F) K (a i / a j) ∈ p.ring := by
  classical
  let S := Finset.univ.filter fun i => a i ≠ 0
  obtain ⟨i0,h0⟩ := ha
  have hn : S.Nonempty := ⟨i0,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h0⟩⟩
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image (fun i => (a i).intDegree) hn
  have hj0 := (Finset.mem_filter.mp hj).2
  refine ⟨j,hj0,?_⟩
  intro p hp i
  by_cases hi : a i = 0
  · simpa [hi] using p.ring.zero_mem
  apply regular_scalar_of_degree_nonpos K p hp
  have hm := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  have he := RatFunc.intDegree_mul (div_ne_zero hi hj0) hj0
  rw [div_mul_cancel₀ _ hj0] at he
  omega

/-- Regular scalar functions at a pole on a cubic branch. -/
theorem regular_of_degree_nonpos {R : Finset (Line F)} (D : Branch F R) (p : Place D)
    (hp : parameter D ∉ p.ring) (a : RatFunc F) (ha : a.intDegree ≤ 0) :
    algebraMap (RatFunc F) D.K a ∈ p.ring :=
  regular_scalar_of_degree_nonpos D.K p hp a ha

/-- The coefficient normalization for a cubic branch. -/
theorem normalize {R : Finset (Line F)} (D : Branch F R) {I : Type*} [Fintype I] (a : I → RatFunc F)
    (ha : ∃ i, a i ≠ 0) : ∃ j, a j ≠ 0 ∧ ∀ p : Place D, parameter D ∉ p.ring →
      ∀ i, algebraMap (RatFunc F) D.K (a i / a j) ∈ p.ring :=
  normalize_field D.K a ha

end BlockingCurves.CubicPoleScalars
