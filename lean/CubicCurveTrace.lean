import CubicMonodromy
import CubicPairCount
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Polynomial.Derivative

open Polynomial

/-! The fixed-slope curve of §18. The finite sums below are defined from the
actual cubic fibers. Cohomological dimensions, local conductors and eigenvalues
are explicit inputs to the numerical forms of the classical theorems. -/
namespace BlockingCurves.CubicCurveTrace
open Finset BigOperators CubicCharacters CubicPairCount CubicMonodromy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def base (S : Finset F) := (S.image fun a => -a)ᶜ
def roots (b a : F) : ℕ := (univ.filter fun x : F => x^3 - x - b = a).card

/-- In a uniformizer at the double root x=1 the special cubic is Z²(1+Z)
and its derivative is Z². These are identities over any field of characteristic 2. -/
theorem wild_local_equations {K : Type*} [Field K] [CharP K 2] :
    ((X+1)^3-(X+1) : K[X]) = X^2*(1+X) ∧
    derivative ((X+1)^3-(X+1) : K[X]) = X^2 := by
  have h2 : (2 : K[X]) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3 : K[X]) = 1 := by linear_combination h2
  constructor
  · calc
      _ = X^2*(1+X) + 2*(X^2+X) := by ring
      _ = _ := by rw [h2]; ring
  · rw [derivative_sub, derivative_pow, derivative_add, derivative_X, derivative_one]
    simp
    linear_combination ((X : K[X])+1)^2*h3 + (X : K[X])*h2 + h2

/-- At finite intercepts only b=−a can be a branch value; the equivalence
holds over algebraically closed fields as well as over finite fields. -/
theorem wild_critical_iff {K : Type*} [Field K] [CharP K 2] (b a : K) :
    (∃ x : K, x^3-x = b+a ∧ 3*x^2 = 1) ↔ b = -a := by
  have h2 : (2:K) = 0 := CharP.cast_eq_zero _ 2
  have h3 : (3:K) = 1 := by linear_combination h2
  constructor
  · rintro ⟨x,hx,hd⟩
    rw [h3, one_mul] at hd
    rw [pow_succ, hd, one_mul, sub_self] at hx
    exact eq_neg_of_add_eq_zero_left hx.symm
  · rintro rfl
    exact ⟨1, by simp, by simp [h3]⟩

theorem roots_zero_iff (b a : F) : roots b a = 0 ↔ ∀ x : F, x^3 - x - b ≠ a := by
  simp [roots, Finset.card_eq_zero, Finset.eq_empty_iff_forall_not_mem]

theorem base_card (S : Finset F) : (base S).card = Fintype.card F - S.card := by
  rw [base, Finset.card_compl, Finset.card_image_of_injective _ neg_injective]

theorem counted_fibers (S : Finset F) :
    ((base S).filter fun b => ∀ a : S, roots b (a : F) = 0).card = fixedEscapeCount S := by
  unfold fixedEscapeCount
  apply congrArg Finset.card
  ext b
  simp only [base, Finset.mem_filter, mem_compl, mem_image, fixedEscapeCount,
    mem_univ, true_and, Subtype.forall, roots_zero_iff, not_exists, not_and]
  constructor
  · rintro ⟨hb, hx⟩ a ha
    exact ⟨Ne.symm (hb a ha), hx a ha⟩
  · intro h
    exact ⟨fun a ha => Ne.symm (h a ha).1, fun a ha => (h a ha).2⟩

/-- Finite numerical data for compactly supported cohomology on the punctured
line. The two lists count eigenvalues with algebraic multiplicity. -/
structure CurveData (I : Type*) where
  dimOne : ℕ
  dimTwo : ℕ
  frobOne : Fin dimOne → ℂ
  frobTwo : Fin dimTwo → ℂ
  swan : I → ℕ
  swanInfinity : ℕ
  inertiaFixed : I → ℕ

/-- Real part of the Grothendieck trace formula (H⁰_c is zero on this open curve). -/
def traceFormula {I : Type*} (D : CurveData I) (localSum : ℝ) :=
  localSum = (∑ j, (D.frobTwo j).re) - ∑ j, (D.frobOne j).re

/-- The Euler characteristic with the local Swan terms, including infinity. -/
def conductorFormula {I : Type*} [Fintype I] (D : CurveData I) (r : ℝ) :=
  (D.dimOne : ℝ) - D.dimTwo =
    (Fintype.card I - 1 : ℝ)*r + (∑ i, (D.swan i : ℝ)) + D.swanInfinity

theorem word_estimate {I : Type*} [Fintype I] {D : CurveData I} {r q t : ℝ}
    (htrace : traceFormula D t) (hgos : conductorFormula D r)
    (htop : D.dimTwo = 0) (htame : D.swanInfinity = 0)
    (hswan : ∀ i, (D.swan i : ℝ) ≤ r)
    (hweight : ∀ j, Complex.abs (D.frobOne j) ≤ Real.sqrt q) :
    |t| ≤ (2*(Fintype.card I : ℝ)-1)*r*Real.sqrt q := by
  classical
  have hz : IsEmpty (Fin D.dimTwo) := by rw [htop]; infer_instance
  have ht : t = -(∑ j, (D.frobOne j).re) := by simpa [traceFormula] using htrace
  have hs := Finset.sum_le_sum (s := (univ : Finset I)) (fun i _ => hswan i)
  simp only [sum_const, card_univ, nsmul_eq_mul] at hs
  unfold conductorFormula at hgos
  rw [htop, htame] at hgos
  push_cast at hgos
  have hd : (D.dimOne : ℝ) ≤ (2*(Fintype.card I : ℝ)-1)*r := by linarith
  rw [ht, abs_neg]
  calc
    _ ≤ ∑ j, |(D.frobOne j).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin D.dimOne, Real.sqrt q := Finset.sum_le_sum fun j _ =>
      (Complex.abs_re_le_abs _).trans (hweight j)
    _ = (D.dimOne : ℝ)*Real.sqrt q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hd (Real.sqrt_nonneg _)

/-- Geometric inputs at slope one. The finite conductor equality is the Swan
formula for an order-two inertia group with a single lower break at one.
The separate top-degree identity expresses duality via the invariant character.
The fields describe the actual character sums on the punctured line. -/
structure CurveLaws (S : Finset F) (D : Word S → CurveData S)
    (G : Subgroup (S → SymThree)) : Prop where
  transitive : transitiveFactors G
  isolatedInertia : supportedInertia G
  trace : ∀ w ∈ nontrivialWords S, traceFormula (D w)
    (characterSum (base S) (fun b (a : S) => roots b a) w)
  gos : ∀ w ∈ nontrivialWords S, conductorFormula (D w) (rank w)
  dual : ∀ w ∈ nontrivialWords S, topMultiplicity G w (D w).dimTwo
  tameInfinity : ∀ w ∈ nontrivialWords S, (D w).swanInfinity = 0
  swanAtShift : ∀ w ∈ nontrivialWords S, ∀ a,
    ((D w).swan a : ℝ) + (D w).inertiaFixed a = rank w
  weightOne : ∀ w ∈ nontrivialWords S, ∀ j, Complex.abs ((D w).frobOne j) ≤
    Real.sqrt (Fintype.card F)

/-- Uniform fixed-slope estimate on the actual count, for all field sizes
and all shift sets for which the local geometric laws hold. -/
theorem fixed_deviation_of_curve_data (S : Finset F) (D : Word S → CurveData S)
    (G : Subgroup (S → SymThree)) (law : CurveLaws S D G) :
    CubicAsymptotics.fixedSlopeDeviation (Fintype.card F) S.card (fixedEscapeCount S) := by
  classical
  have hc := centered_count (base S) (fun b (a : S) => roots b a)
  rw [counted_fibers, base_card, Nat.cast_sub (Finset.card_le_univ S), Fintype.card_coe] at hc
  unfold CubicAsymptotics.fixedSlopeDeviation
  rw [hc]
  calc
    _ ≤ ∑ w ∈ nontrivialWords S, |coefficient w * characterSum (base S)
          (fun b (a : S) => roots b a) w| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ nontrivialWords S, (2*(S.card:ℝ)-1)*rank w*Real.sqrt (Fintype.card F) := by
      apply Finset.sum_le_sum
      intro w hw
      rw [abs_mul, abs_coefficient, one_mul]
      have htop := top_eq_zero G (full_of_inertia G law.transitive law.isolatedInertia) hw (law.dual w hw)
      have hlocal (a : S) : ((D w).swan a : ℝ) ≤ rank w := by
        rw [← law.swanAtShift w hw a]
        exact le_add_of_nonneg_right (Nat.cast_nonneg _)
      simpa using word_estimate (law.trace w hw) (law.gos w hw) htop
        (law.tameInfinity w hw) hlocal (law.weightOne w hw)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum, sum_nontrivial_ranks]; simp

/-- The denominator log 16 in §18, with the point-count estimate derived above. -/
theorem fixed_lower_of_curve_data (S : Finset F) (hlarge : 16 ≤ (Fintype.card F : ℝ))
    (D : Word S → CurveData S) (G : Subgroup (S → SymThree)) (law : CurveLaws S D G)
    (hblocks : ProjectiveBlocks 3 (S : Set F)) :
    (Real.log (Fintype.card F) - 2 * Real.log (Real.log (Fintype.card F))) /
      Real.log 16 < (S.card : ℝ) :=
  fixed_blocking_card_lower_of_trace S hlarge (fixed_deviation_of_curve_data S D G law) hblocks

end BlockingCurves.CubicCurveTrace
