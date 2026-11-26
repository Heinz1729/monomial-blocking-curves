import CubicCurveTrace
import CubicSurfaceTrace
import CubicRationalRoots
import Mathlib.FieldTheory.Separable

/-! Bézout certificates for the two open loci used in the cubic trace formulas. -/
namespace BlockingCurves.CubicUnramified
open Polynomial CubicPairCount
variable {K : Type*} [Field K]

noncomputable def cubic (t : K) : K[X] := X^3 - 3*X - C t

theorem separable_of_discriminant (t : K) (h3 : (3 : K) ≠ 0) (h : t^2 ≠ 4) :
    (cubic t).Separable := by
  let A : K[X] := -3*(2*X - C t)
  let B : K[X] := (2*X - C t)*X - 4
  let d : K := 3*(4-t^2)
  have hd : d ≠ 0 := mul_ne_zero h3 (sub_ne_zero.mpr h.symm)
  have cert : A*cubic t + B*(derivative (cubic t)) = C d := by
    simp [A, B, d, cubic, derivative_sub, derivative_mul, derivative_pow]
    ring
  rw [Polynomial.separable_def]
  refine ⟨C d⁻¹*A, C d⁻¹*B, ?_⟩
  rw [mul_assoc (C d⁻¹) A, mul_assoc (C d⁻¹) B, ← mul_add, cert,
    ← map_mul, inv_mul_cancel hd, map_one]

/-- The actual ordered-pair base removes precisely the two finite discriminant factors. -/
theorem surface_separable {v w a : K} (hd : v ≠ w) (hv : v ≠ -a) (hw : w ≠ -a)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) : (cubic (parameter v w a)).Separable := by
  apply separable_of_discriminant _ h3
  have hdiff : v-w ≠ 0 := sub_ne_zero.mpr hd
  have hy : parameter v w a ^ 2 - 4 = 2^4*(v+a)*(w+a)/(v-w)^2 := by
    unfold parameter
    field_simp
    ring
  apply sub_ne_zero.mp
  rw [hy]
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2)
    (by simpa [eq_neg_iff_add_eq_zero] using hv)) (by simpa [eq_neg_iff_add_eq_zero] using hw))
    (pow_ne_zero _ hdiff)

theorem fixed_separable [CharP K 2] {b a : K} (h : b ≠ -a) :
    (X^3 - X - C (b+a) : K[X]).Separable := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : K) = 1 := by linear_combination h2
  have h4 : (4 : K) = 0 := by linear_combination 2*h2
  have hd : (b+a)^2 ≠ 4 := by
    rw [h4]
    exact pow_ne_zero _ (fun hz => h (eq_neg_of_add_eq_zero_left hz))
  have hp : (3 : K[X]) = 1 := by linear_combination (CharP.cast_eq_zero K[X] 2)
  simpa [cubic, hp] using separable_of_discriminant (b+a) (h3 ▸ one_ne_zero) hd

section Counts
open Finset
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Field K] [Algebra F K]

noncomputable def fixedGeometricRoots (K : Type*) [Field K] [Algebra F K] (m t : F) : ℕ := by
  classical
  exact (((X^3-C m*X-C t : F[X]).map (algebraMap F K)).roots.toFinset.filter
    fun z => z^Fintype.card F = z).card

theorem fixedGeometricRoots_eq (m t : F) :
    fixedGeometricRoots K m t = (univ.filter fun x : F => x^3-m*x = t).card := by
  classical
  exact CubicRationalRoots.cubic_fixed_count (K := K) m t

/-- The local term of the surface trace is the Frobenius root count. -/
theorem surface_frobenius_count (P : F × F) (a : F) :
    fixedGeometricRoots K 3 (parameter P.1 P.2 a) = CubicSurfaceTrace.rootCount P a :=
  fixedGeometricRoots_eq _ _

/-- The local term of the fixed-slope trace is the same Frobenius count. -/
theorem curve_frobenius_count (b a : F) :
    fixedGeometricRoots K 1 (b+a) = CubicCurveTrace.roots b a := by
  rw [fixedGeometricRoots_eq]
  unfold CubicCurveTrace.roots
  apply congrArg Finset.card
  ext x
  simp only [mem_filter,mem_univ,true_and,one_mul]
  constructor <;> intro he <;> linear_combination he

end Counts
end BlockingCurves.CubicUnramified
