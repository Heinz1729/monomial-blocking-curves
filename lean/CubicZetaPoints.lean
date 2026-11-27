import CubicPoleFibre
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Complex.Abs

/-! The coefficient-one implication of the Weil zeta theorem, with a
coefficientwise Euler product over the actual closed places of a branch. -/
noncomputable section
namespace BlockingCurves.CubicZetaPoints
open CubicAlteration CubicRepairPlaces Finset PowerSeries BigOperators
universe u
variable {F : Type u} [Field F] {R : Finset (Line F)}

abbrev GroundRing (D : Branch F R) :=
  {O : ValuationSubring D.K // ∀ a : F, constant D a ∈ O}

def constantResidue (D : Branch F R) (v : GroundRing D) :
    F →+* LocalRing.ResidueField v.val :=
  (LocalRing.residue v.val).comp ((constant D).codRestrict v.val v.property)

def residueDegree (D : Branch F R) (v : GroundRing D) : ℕ := by
  letI := (constantResidue D v).toAlgebra
  exact FiniteDimensional.finrank F (LocalRing.ResidueField v.val)

/-- Index zero means residue degree one; only positive degrees occur in the product. -/
abbrev ClosedPoint (D : Branch F R) (i : ℕ) := {v : GroundRing D // residueDegree D v = i+1}

private def firstPlace (D : Branch F R) (v : ClosedPoint D 0) : Place D := by
  let O := v.val.val
  let f : F →+* LocalRing.ResidueField O := constantResidue D v.val
  letI := f.toAlgebra
  have hd : FiniteDimensional.finrank F (LocalRing.ResidueField O) = 1 := v.property
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨a,ha⟩ := (finrank_eq_one_iff_of_nonzero' (1 : LocalRing.ResidueField O) one_ne_zero).mp hd y
    exact ⟨a,by simpa [Algebra.smul_def] using ha⟩
  let e := RingEquiv.ofBijective f ⟨f.injective,hsur⟩
  refine ⟨O,v.val.property,e.symm.toRingHom.comp (LocalRing.residue O),?_⟩
  intro a
  exact e.symm_apply_apply a

def degreeOneEmbedding (D : Branch F R) : ClosedPoint D 0 ↪ Place D where
  toFun := firstPlace D
  inj' := by
    intro v w h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg RationalPlace.ring h

/-- The chosen residue identification in a rational place is forced by its
values on F. It is equivalent to having residue degree one. -/
def degreeOneEquiv (D : Branch F R) : ClosedPoint D 0 ≃ Place D := by
  apply Equiv.ofBijective (degreeOneEmbedding D)
  refine ⟨(degreeOneEmbedding D).injective,?_⟩
  intro p
  let v : GroundRing D := ⟨p.ring,p.constants⟩
  have hk := LocalRing.ker_eq_maximalIdeal p.residue (fun a => ⟨_,p.on_constants a⟩)
  let lift : LocalRing.ResidueField p.ring →+* F :=
    Ideal.Quotient.lift _ p.residue (fun a ha => by rwa [← hk, RingHom.mem_ker] at ha)
  have h : ∀ a : F, lift (constantResidue D v a) = a := p.on_constants
  have hd : residueDegree D v = 1 := by
    letI := (constantResidue D v).toAlgebra
    apply (finrank_eq_one_iff_of_nonzero' (1 : LocalRing.ResidueField p.ring) one_ne_zero).2
    intro y
    refine ⟨lift y,?_⟩
    rw [Algebra.smul_def,mul_one]
    exact lift.injective (h (lift y))
  exact ⟨⟨v,hd⟩, CubicPoleFibre.place_ext rfl⟩

/-- Coefficients of the local factor 1/(1−Tᵈ), for d>0. -/
def eulerFactor (d : ℕ) : PowerSeries ℂ := mk fun n => if d ∣ n then 1 else 0

theorem eulerFactor_inverse (d : ℕ) (hd : 0 < d) :
    eulerFactor d * (1-(X : PowerSeries ℂ)^d) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one]
  simp only [eulerFactor, coeff_mk]
  by_cases hn : d ≤ n
  · have hor : d ∣ n-d ↔ d ∣ n := by
      conv_rhs => rw [← Nat.sub_add_cancel hn]
      simp
    simp [hn,hor,show n ≠ 0 by omega]
  · by_cases hz : n=0
    · simp [hz,show d ≠ 0 by omega]
    · have hnot : ¬ d ∣ n := fun h => hn (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h)
      simp [hn,hz,hnot]

/-- To extract coefficient n of the Euler product one needs just degrees
1,...,n. Each exponent is the number of closed places of that residue degree. -/
def zeta (D : Branch F R) : PowerSeries ℂ := mk fun n =>
  coeff ℂ n (∏ i ∈ range n, (eulerFactor (i+1))^(Nat.card (ClosedPoint D i)))

private theorem first_terms (A : PowerSeries ℂ) {n d : ℕ} (hd : n < d) :
    coeff ℂ n (A*eulerFactor d) = coeff ℂ n A := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (n,0)]
  · simp [eulerFactor]
  · rintro ⟨i,j⟩ h hij
    have he : i+j = n := mem_antidiagonal.mp h
    have hj : j ≠ 0 := by
      intro hz
      subst j
      simp_all
    have hnd : ¬ d ∣ j := fun he' => by have := Nat.le_of_dvd (Nat.pos_of_ne_zero hj) he'; omega
    simp [eulerFactor,hnd]
  · simp

/-- Enlarging the degree cutoff cannot change a coefficient already computed. -/
theorem zeta_coefficient (D : Branch F R) {n N : ℕ} (hn : n ≤ N) :
    coeff ℂ n (zeta D) =
      coeff ℂ n (∏ i ∈ range N, (eulerFactor (i+1))^(Nat.card (ClosedPoint D i))) := by
  induction N, hn using Nat.le_induction with
  | base => simp [zeta]
  | succ k hk ih =>
    rw [prod_range_succ,ih]
    let A := ∏ i ∈ range k, (eulerFactor (i+1))^(Nat.card (ClosedPoint D i))
    change coeff ℂ n A = coeff ℂ n (A*(eulerFactor (k+1))^(Nat.card (ClosedPoint D k)))
    generalize Nat.card (ClosedPoint D k) = j
    induction j with
    | zero => simp
    | succ j hj => simpa only [pow_succ,← mul_assoc,first_terms _ (Nat.lt_succ_of_le hk)] using hj

private theorem first_mul (A B : PowerSeries ℂ) :
    coeff ℂ 1 (A*B) = constantCoeff ℂ A * coeff ℂ 1 B + coeff ℂ 1 A * constantCoeff ℂ B := by
  rw [coeff_mul, show Finset.antidiagonal 1 = {(0,1),(1,0)} by decide]
  simp [coeff_zero_eq_constantCoeff_apply]

private theorem first_pow (A : PowerSeries ℂ) (h : constantCoeff ℂ A = 1) (n : ℕ) :
    coeff ℂ 1 (A^n) = n * coeff ℂ 1 A := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ,first_mul,ih,map_pow,h]
    push_cast
    ring

@[simp] theorem zeta_constant (D : Branch F R) : constantCoeff ℂ (zeta D) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  simp [zeta,coeff_one]

theorem zeta_first (D : Branch F R) : coeff ℂ 1 (zeta D) = Nat.card (ClosedPoint D 0) := by
  have h : constantCoeff ℂ (eulerFactor 1) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]; simp [eulerFactor]
  simp only [zeta, coeff_mk, range_one, prod_singleton, zero_add]
  rw [first_pow _ h]
  simp [eulerFactor]

private def linearFactor (a : ℂ) : PowerSeries ℂ := 1 - C ℂ a*X

private theorem linear_zero (a : ℂ) : constantCoeff ℂ (linearFactor a) = 1 := by
  simp [linearFactor]

private theorem linear_first (a : ℂ) : coeff ℂ 1 (linearFactor a) = -a := by
  simp [linearFactor,coeff_one]

private theorem numerator_first {I : Type*} (s : Finset I) (a : I → ℂ) :
    coeff ℂ 1 (∏ i ∈ s, linearFactor (a i)) = -∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeff_one]
  | @insert i s hi ih =>
    rw [prod_insert hi,sum_insert hi,first_mul,linear_zero,linear_first,ih,map_prod]
    simp [linear_zero]

/-- The two linear denominator factors of a smooth proper curve over F_q. -/
def denominator (q : ℕ) : PowerSeries ℂ := linearFactor 1 * linearFactor q

/-- The standard factorization of the Euler product and the individual
weight-one upper bounds. Finiteness is explicit so no infinite cardinal can
silently contribute zero through Nat.card. -/
structure WeilLaws (D : Branch F R) (q g : ℕ) : Prop where
  finiteClosed : ∀ i, Finite (ClosedPoint D i)
  spectrum : ∃ α : Fin (2*g) → ℂ,
    denominator q * zeta D = ∏ i, (1 - C ℂ (α i)*X) ∧
    ∀ i, Complex.abs (α i) ≤ Real.sqrt q

theorem degree_one_trace (D : Branch F R) {q g : ℕ} (a : Fin (2*g) → ℂ)
    (h : denominator q * zeta D = ∏ i, (1-C ℂ (a i)*X)) :
    (Nat.card (ClosedPoint D 0) : ℂ) = q+1-∑ i, a i := by
  have h1 := congrArg (coeff ℂ 1) h
  change coeff ℂ 1 (denominator q * zeta D) = coeff ℂ 1 (∏ i, linearFactor (a i)) at h1
  rw [denominator,first_mul,first_mul,numerator_first,map_mul,
    linear_first,linear_first,linear_zero,linear_zero,zeta_constant,zeta_first] at h1
  linear_combination h1

/-- Taking the degree-one trace and bounding each weight gives both sides of
Hasse–Weil for the complete set of rational places. -/
theorem rational_point_estimate (D : Branch F R) {q g : ℕ} (W : WeilLaws D q g) :
    |(Nat.card (Place D) : ℝ) - ((q:ℝ)+1)| ≤ 2*(g:ℝ)*Real.sqrt q := by
  obtain ⟨a,he,hwt⟩ := W.spectrum
  have ht := congrArg Complex.re (degree_one_trace D a he)
  simp [Complex.sub_re,Complex.add_re,Complex.re_sum] at ht
  rw [← Nat.card_congr (degreeOneEquiv D), ht, sub_sub_cancel_left, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hsum := Finset.sum_le_sum (s := (univ : Finset (Fin (2*g))))
    fun i _ => (Complex.abs_re_le_abs (a i)).trans (hwt i)
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] using hsum

theorem point_lower (D : Branch F R) {q g : ℕ} (W : WeilLaws D q g) :
    (q:ℝ)+1-2*(g:ℝ)*Real.sqrt q ≤ Nat.card (ClosedPoint D 0) := by
  have h := (abs_le.mp (rational_point_estimate D W)).1
  rw [← Nat.card_congr (degreeOneEquiv D)] at h
  linarith

end BlockingCurves.CubicZetaPoints
