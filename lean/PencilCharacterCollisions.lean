import PencilCollisionCover
import PencilHorizontal
import Mathlib.FieldTheory.Perfect
import Mathlib.Data.Nat.Factorization.Basic

/-! Frobenius changes of coordinates remove both inseparable factors from the
ordered collision equation. The only geometric input below is a tame affine
Kummer point estimate for squarefree, nonconstant polynomials. -/

namespace BlockingCurves.PencilCharacterCollisions

open Polynomial PencilCollisionCover PencilSampling
open scoped Polynomial
noncomputable section

variable {F : Type*} [Field F] [Fintype F]
attribute [local instance] Classical.propDecidable
local instance : DecidableEq F := Classical.decEq _

def difference (F : Type*) [Field F] (e : ℕ) : F[X] := (X+1)^e-X^e

def kummerPoints (P : F[X]) (k : ℕ) (a : F) : Finset (F × F) :=
  Finset.univ.filter (fun w => w.2^k * P.eval w.1 = a)

/-- The nonvanishing of the derivative at every geometric zero is tested in the
algebraic closure, including when the characteristic divides e-1. -/
theorem difference_simple {e : ℕ} (he : 1 < e) (hc : (e:F) ≠ 0) (t : AlgebraicClosure F)
    (ht : aeval t (difference F e) = 0) :
    aeval t (derivative (difference F e)) ≠ 0 := by
  have hcast : (e : AlgebraicClosure F) ≠ 0 := by
    exact_mod_cast (show algebraMap F (AlgebraicClosure F) (e:F) ≠ 0 by
      simpa using (algebraMap F (AlgebraicClosure F)).injective.ne hc)
  have hpow : (t+1)^e=t^e := by simpa [difference,sub_eq_zero] using ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    simp [zero_pow (by omega : e ≠ 0)] at hpow
  intro hd
  have h' : (e:AlgebraicClosure F) * (t+1)^(e-1) = (e:AlgebraicClosure F)*t^(e-1) := by
    simpa [difference,derivative_pow,derivative_add,sub_eq_zero] using hd
  have hh := mul_left_cancel₀ hcast h'
  have hsucc : e-1+1=e := by omega
  rw [← hsucc] at hpow
  simp only [pow_succ, hh] at hpow
  exact one_ne_zero (by linear_combination (mul_left_cancel₀ (pow_ne_zero _ ht0) hpow))

theorem difference_degree {e : ℕ} (he : 0 < e) (hc : (e:F) ≠ 0) :
    (difference F e).natDegree = e-1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero he.ne'
  simp only [Nat.succ_sub_one]
  apply le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.2
    intro j hj
    by_cases h : j=k+1
    · simp [difference,h,coeff_X_add_one_pow,coeff_X_pow]
    · simp [difference,coeff_X_add_one_pow,coeff_X_pow, h, Ne.symm h,
        Nat.choose_eq_zero_of_lt (show k+1<j by omega)]
  · apply le_natDegree_of_ne_zero
    simpa [difference, coeff_X_add_one_pow, coeff_X_pow, Nat.choose_succ_self_right] using hc

/-- Standard affine Kummer point bound. For y^k P(t)=a (a nonzero, k tame,
P nonconstant and geometrically squarefree), the smooth completion has
2g ≤ (k−1)(deg P−1); the weaker displayed constant also covers linear P. -/
def AffineKummerBound (F : Type*) [Field F] [Fintype F] : Prop :=
  ∀ (P : F[X]) (k : ℕ) (a : F), 0 < P.natDegree → 0 < k → (k:F) ≠ 0 → a ≠ 0 →
    (∀ t : AlgebraicClosure F, aeval t P=0 → aeval t (derivative P) ≠ 0) →
    ((kummerPoints P k a).card : ℝ) ≤ Fintype.card F + 1 +
      ((k-1 : ℕ) : ℝ) * P.natDegree * Real.sqrt (Fintype.card F)

private theorem collision_iff {x y m b : F} {d : ℕ} (hd : 2 ≤ d) (hne : x-y ≠ 0) :
    (x^d-m*x-b=y^d-m*y-b) ↔
      (x-y)^(d-1) * (((y/(x-y))+1)^d-(y/(x-y))^d)=m := by
  let t := y/(x-y)
  have hy : t*(x-y)=y := div_mul_cancel₀ _ hne
  have hx : (t+1)*(x-y)=x := by linear_combination hy
  have hpow : ((x-y)^(d-1) * ((t+1)^d-t^d)) * (x-y) = x^d-y^d := by
    calc
      _ = ((t+1)^d-t^d)*(x-y)^d := by
        have hnorm : (x-y)^(d-1)*(x-y) = (x-y)^d := by rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ d)]
        rw [← hnorm]
        ac_rfl
      _ = _ := by rw [sub_mul, ← mul_pow, ← mul_pow, hx, hy]
  change _ ↔ (x-y)^(d-1)*((t+1)^d-t^d)=m
  constructor
  · intro h
    apply mul_right_cancel₀ hne
    linear_combination hpow + h
  · intro h
    rw [h] at hpow
    linear_combination -hpow

private def pairEquiv (A B : F ≃+* F) :
    {xy : F × F // xy.1 ≠ xy.2} ≃ {tz : F × F // tz.2 ≠ 0} where
  toFun := fun ⟨⟨x,y⟩,h⟩ => ⟨(A (y/(x-y)), B (x-y)), by exact fun he => (sub_ne_zero.mpr h) (B.injective (he.trans (map_zero B).symm))⟩
  invFun := fun ⟨⟨t,z⟩,hz⟩ => ⟨((A.symm t+1)*B.symm z,A.symm t*B.symm z), by
    intro he
    have hz' : B.symm z ≠ 0 := by simpa using hz
    exact hz' (by linear_combination he)⟩
  left_inv := by
    rintro ⟨⟨x,y⟩,h⟩
    apply Subtype.ext
    apply Prod.ext
    · simp only [RingEquiv.symm_apply_apply]
      change (y/(x-y)+1)*(x-y)=x
      rw [add_mul, div_mul_cancel₀ _ (sub_ne_zero.mpr h), one_mul]
      ring
    · exact (by simp [div_mul_cancel₀ _ (sub_ne_zero.mpr h)])
  right_inv := by
    rintro ⟨⟨t,z⟩,h⟩
    have hz : B.symm z ≠ 0 := by simpa using h
    have he : (A.symm t+1)*B.symm z - A.symm t*B.symm z = B.symm z := by ring
    apply Subtype.ext
    apply Prod.ext <;> simp [he, hz]

theorem collision_kummer_count {d e k v w p : ℕ} [Fact p.Prime] [CharP F p]
    (hd : 2 ≤ d) (de : d=p^v*e) (dk : d-1=p^w*k) (hk : 0 < k)
    (m b : F) (hm : m ≠ 0) :
    (offDiagonal (fun x : F => x^d-m*x-b)).card = (kummerPoints (difference F e) k m).card := by
  classical
  let A := iterateFrobeniusEquiv F p v
  let B := iterateFrobeniusEquiv F p w
  let g := pairEquiv A B
  let C := offDiagonal (fun x : F => x^d-m*x-b)
  let K := kummerPoints (difference F e) k m
  have hc (x : {xy : F×F // xy.1 ≠ xy.2}) : x.1 ∈ C ↔ (g x).1 ∈ K := by
    obtain ⟨⟨x,y⟩,h⟩ := x
    change x ≠ y at h
    simp only [C, K, offDiagonal, kummerPoints, Finset.mem_filter, Finset.mem_univ, true_and,
      h, collision_iff hd (sub_ne_zero.mpr h)]
    rw [and_iff_right h]
    let t := y/(x-y)
    change (x-y)^(d-1)*((t+1)^d-t^d)=m ↔ (B (x-y))^k * (difference F e).eval (A t)=m
    simp only [difference,eval_sub,eval_pow,eval_add,eval_X,eval_one]
    have addA : A t + 1 = A (t+1) := by simp
    rw [addA, dk, de]
    simp only [pow_mul]
    rfl
  have f (x : C) : x.1.1 ≠ x.1.2 := (Finset.mem_filter.1 x.2).2.1
  have hK (z : K) : z.1.2 ≠ 0 := by
    intro h
    have H := (Finset.mem_filter.1 z.2).2
    change z.1.2^k * _ = m at H
    rw [h, zero_pow hk.ne', zero_mul] at H
    exact hm H.symm
  let eqv : (C : Type _) ≃ (K : Type _) :=
    { toFun := fun x => ⟨(g ⟨x.1,f x⟩).1, (hc _).1 x.2⟩
      invFun := fun z => ⟨(g.symm ⟨z.1,hK z⟩).1, (hc _).2 (by simp [z.2])⟩
      left_inv := fun x => Subtype.ext (congrArg (fun w : {xy : F×F // xy.1 ≠ xy.2} => w.val) (g.symm_apply_apply ⟨x.1,f x⟩))
      right_inv := fun z => Subtype.ext (congrArg (fun w : {tz : F×F // tz.2 ≠ 0} => w.val) (g.apply_symm_apply ⟨z.1,hK z⟩)) }
  simpa only [Fintype.card_coe] using Fintype.card_congr eqv

/-- For d=2p^v (odd p), the tame polynomial is affine linear. Every nonzero z
gives exactly one t, so the true ordered collision count is q-1 without Weil. -/
theorem doubled_frobenius_collisions {d p v : ℕ} [Fact p.Prime] [CharP F p]
    (h2 : (2:F) ≠ 0) (hd : d=p^v*2) (m b : F) (hm : m≠0) :
    (offDiagonal (fun x : F => x^d-m*x-b)).card = Fintype.card F-1 := by
  classical
  have hdeg : 2 ≤ d := hd.symm ▸ Nat.le_mul_of_pos_left _ (pow_pos (Fact.out : p.Prime).pos _)
  rw [collision_kummer_count hdeg hd (w := 0) (k := d-1) (by simp) (by omega) m b hm]
  let K := kummerPoints (difference F 2) (d-1) m
  have heval (x : F) : (difference F 2).eval x = 2*x+1 := by simp [difference]; ring
  have hK (z : K) : z.1.2^(d-1)*(2*z.1.1+1)=m := by
    have h := (Finset.mem_filter.1 z.2).2
    simpa only [heval] using h
  have hnz (z : K) : z.1.2 ≠ 0 := by
    intro hz
    exact hm (by simpa [hz, zero_pow (by omega : d-1 ≠ 0)] using (hK z).symm)
  let f : K → Fˣ := fun z => Units.mk0 z.1.2 (hnz z)
  have hi : Function.Injective f := by
    intro x y hh
    have he : x.1.2=y.1.2 := congrArg Units.val hh
    have h := (hK x).trans (hK y).symm
    rw [he] at h
    have ht := mul_left_cancel₀ (pow_ne_zero _ (hnz y)) h
    exact Subtype.ext (Prod.ext (mul_left_cancel₀ h2 (add_right_cancel ht)) he)
  have hs : Function.Surjective f := by
    intro z
    let w := (z:F)^(d-1)
    have hw : w≠0 := pow_ne_zero _ z.ne_zero
    let t := (m/w-1)/2
    have he : w*(2*t+1)=m := by dsimp [t]; field_simp [hw,h2]; ring
    refine ⟨⟨(t,(z:F)), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩⟩, Units.ext rfl⟩
    change w*(difference F 2).eval t=m
    rwa [heval]
  simpa only [Fintype.card_coe, Fintype.card_units] using Fintype.card_of_bijective ⟨hi,hs⟩

/-- The normalized Weil input controls the collision count at every nonzero slope,
including in characteristics dividing either d or d-1. -/
theorem collision_upper_of_kummer {d : ℕ} (hd : 2 ≤ d)
    (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v) (weil : AffineKummerBound F)
    (m b : F) (hm : m ≠ 0) :
    ((offDiagonal (fun x : F => x^d-m*x-b)).card : ℝ) ≤
      Fintype.card F + 1 + (d:ℝ)^2 * Real.sqrt (Fintype.card F) := by
  let p := ringChar F
  have hp := CharP.char_is_prime F p
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨v,e,hpe,de⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : d ≠ 0) p hp.ne_one
  obtain ⟨w,k,hpk,dk⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : d-1 ≠ 0) p hp.ne_one
  have he : 1 < e := by
    by_contra! h
    interval_cases e
    · simp at de; omega
    · exact nonpower v (by simpa using de)
  have hk : 0 < k := by
    by_contra! hz
    have : k = 0 := by omega
    simp [this] at dk
    omega
  have he' : (e:F) ≠ 0 := fun h => hpe ((CharP.cast_eq_zero_iff F p _).1 h)
  have hk' : (k:F) ≠ 0 := fun h => hpk ((CharP.cast_eq_zero_iff F p _).1 h)
  have hdeg := difference_degree he.le he'
  rw [collision_kummer_count hd de dk hk m b hm]
  have hb := weil (difference F e) k m (by rw [hdeg]; omega) hk hk' hm (difference_simple he he')
  rw [hdeg] at hb
  apply hb.trans
  have h1 : k ≤ d-1 := dk.symm ▸ Nat.le_mul_of_pos_left _ (pow_pos hp.pos _)
  have h2 : e ≤ d := de.symm ▸ Nat.le_mul_of_pos_left _ (pow_pos hp.pos _)
  have hkR : ((k-1 : ℕ):ℝ) ≤ d := by exact_mod_cast (show k-1 ≤ d by omega)
  have heR : ((e-1 : ℕ):ℝ) ≤ d := by exact_mod_cast (show e-1 ≤ d by omega)
  gcongr
  exact (mul_le_mul hkR heR (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans_eq (sq _).symm

/-- Cauchy–Schwarz turns the Kummer point estimate into a missing-fraction
bound with an explicit uniform constant (1+d²)/4. -/
theorem missed_fraction_of_kummer {d : ℕ} (hd : 2 ≤ d)
    (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v) (weil : AffineKummerBound F)
    (l : Fˣ × F) :
    ((missed d (.inr l : Lines F)).card : ℝ) / Fintype.card F ≤
      1/2 + (1+(d:ℝ)^2)/(4*Real.sqrt (Fintype.card F)) := by
  classical
  let q : ℝ := Fintype.card F
  let f : F → F := fun x => x^d-(l.1:F)*x-l.2
  let I := Finset.univ.image f
  let H := (1+(d:ℝ)^2)*Real.sqrt q
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast (show 1 ≤ Fintype.card F from Fintype.card_pos)
  have hq0 : 0 < q := by linarith
  have hsq : 1 ≤ Real.sqrt q := (Real.one_le_sqrt).2 hq
  have hcol : ((offDiagonal f).card : ℝ) ≤ q+H := by
    apply (collision_upper_of_kummer hd nonpower weil _ _ l.1.ne_zero).trans
    change q + 1 + _ ≤ q + (1+_)*Real.sqrt q
    linarith
  have hcs : q^2 ≤ (I.card:ℝ)*(q+(offDiagonal f).card) := by dsimp [q,I]; exact_mod_cast image_collision_bound f
  have hprod : q^2 ≤ (I.card:ℝ)*(2*q+H) := hcs.trans (mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _))
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hI : q/2-H/4 ≤ I.card := by
    by_contra! h
    have ht := mul_lt_mul_of_pos_right h (show 0 < 2*q+H by linarith)
    nlinarith only [ht, hprod, sq_nonneg H]
  have hM : (missed d (.inr l : Lines F)) = Finset.univ \ I := by
    ext a
    simp [missed,Hits,coordinates,I,f]
  have hcard : ((missed d (.inr l : Lines F)).card : ℝ) + I.card = q := by
    dsimp only [q]
    exact_mod_cast (show (missed d (.inr l : Lines F)).card + I.card = Fintype.card F by
      rw [hM, Finset.card_sdiff (Finset.subset_univ I), Finset.card_univ, Nat.sub_add_cancel (Finset.card_le_univ _)])
  change (_ : ℝ)/q ≤ 1/2+(1+(d:ℝ)^2)/(4*Real.sqrt q)
  apply (div_le_iff hq0).2
  have hr : (1+(d:ℝ)^2)/(4*Real.sqrt q)*q = H/4 := by
    calc
      _ = (1+(d:ℝ)^2)/(4*Real.sqrt q) * (Real.sqrt q)^2 := by rw [Real.sq_sqrt hq0.le]
      _ = _ := by
        dsimp [H]
        field_simp [(Real.sqrt_pos.2 hq0).ne']
        ring_nf
        simp only [Real.sq_sqrt hq0.le]
  rw [add_mul, hr]
  linarith

/-- The nonhorizontal input in the notation of the two-stratum sampling theorems. -/
theorem nonzero_line_bound {d : ℕ} (hd : 2 ≤ d) (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v)
    (weil : AffineKummerBound F) (l : Fˣ × F) :
    ((missed d (.inr l : Lines F)).card:ℝ) ≤
      Fintype.card F*(1/2+((1+(d:ℝ)^2)/4)/Real.sqrt (Fintype.card F)) := by
  have hq : (0:ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos (α := F)
  have h := (div_le_iff hq).1 (missed_fraction_of_kummer hd nonpower weil l)
  simpa only [div_div, mul_comm (Fintype.card F:ℝ)] using h

/-- The only field-theoretic input for the leading coefficient at all non-Frobenius
degrees is the standard affine Kummer point estimate. -/
theorem projective_upper_of_kummer {d : ℕ} (hd : 2 ≤ d)
    (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v) (weil : AffineKummerBound F)
    (hsmall : 1+(d:ℝ)^2 ≤ Real.log 2 * Real.sqrt (Fintype.card F)) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ sampleCutoff (Fintype.card F) (1/2)
        (horizontalRate (d.gcd (Fintype.card F-1)) (Real.log 2)) (Real.log 2)
        ((1+(d:ℝ)^2)/2) + 1 := by
  have h := projective_upper_of_nonzero_value_set hd (δ := 1/2) (C := (1+(d:ℝ)^2)/4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num; linarith) (nonzero_line_bound hd nonpower weil)
  have hr : ((1+(d:ℝ)^2)/4)/(1/2)=(1+(d:ℝ)^2)/2 := by ring
  simpa only [show 1/(1/2:ℝ)=2 by norm_num, hr] using h

/-- With a common repair for the indicated number of lines, the same atomic
Kummer estimate also suffices for the negative log-log correction. -/
theorem projective_loglog_of_kummer {d : ℕ} {c : ℝ} (hd : 2 ≤ d)
    (nonpower : ∀ v : ℕ, d ≠ (ringChar F)^v) (weil : AffineKummerBound F) (hc : 0 < c)
    (hz : 1/2 ≤ c*Real.log (Fintype.card F)) (hzq : c*Real.log (Fintype.card F) ≤ Fintype.card F)
    (hsmall : 1+(d:ℝ)^2 ≤ Real.log 2 * Real.sqrt (Fintype.card F))
    (repair : CommonHit F d ⌊c*Real.log (Fintype.card F)⌋₊) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ max
        ((Real.log (Fintype.card F)-Real.log (Real.log (Fintype.card F))-Real.log c+Real.log 2)/
          horizontalRate (d.gcd (Fintype.card F-1)) (Real.log 2))
        ((2*Real.log (Fintype.card F)-Real.log (Real.log (Fintype.card F))-Real.log c+Real.log 2)/
          Real.log 2 + 12*((1+(d:ℝ)^2)/2)/(Real.log 2)^2) + 2 := by
  have h := projective_loglog_of_nonzero_value_set hd hc hz hzq (δ := 1/2) (C := (1+(d:ℝ)^2)/4)
    (by norm_num) (by norm_num) (by positivity) (by norm_num; linarith)
    (nonzero_line_bound hd nonpower weil) repair
  have hr : ((1+(d:ℝ)^2)/4)/(1/2)=(1+(d:ℝ)^2)/2 := by ring
  simpa only [show 1/(1/2:ℝ)=2 by norm_num, hr] using h

end
end BlockingCurves.PencilCharacterCollisions
