import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The numerical part of the two-parameter cubic estimate, §12 and §16.
The input is the finite trace inequality (12.1) on the actual count.
All constants below are independent of the finite field and the shift set. -/
namespace BlockingCurves.CubicAsymptotics

open Real

/-- The coefficient of the high-weight error, with the choices of zero, one and two
sign positions counted separately. For positive `ell`, the middle term is
also `2 * ell * 2^(ell-1)`. -/
noncomputable def highWeight (ell : ℕ) : ℝ :=
  (6 * (ell : ℝ) + 2) * (2 ^ ell - 1) + ell * 2 ^ ell + ell * (ell - 1 : ℝ) / 2

/-- Equation (12.1). Writing the weight-three term as q √q avoids fractional powers. -/
def traceDeviation (q : ℝ) (ell N : ℕ) : Prop :=
  |(3 : ℝ)^ell * N - (q - ell) * (q - ell - 1)| ≤
    ell * (ell - 1 : ℝ) * (4 ^ ell - 1) * q + highWeight ell * (q + q * √q)

theorem highWeight_le (ell : ℕ) : highWeight ell ≤ 10 * ell * (2:ℝ)^ell := by
  cases ell with
  | zero => norm_num [highWeight]
  | succ k =>
    let n := k+1
    change highWeight n ≤ _
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by dsimp [n]; omega)
    have ha : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow n).le
    have hp : 0 ≤ (2:ℝ)^n := by positivity
    have hfirst := mul_le_mul_of_nonneg_right h1 hp
    have hlast := mul_le_mul_of_nonneg_left ha (show 0 ≤ (n:ℝ) by positivity)
    change highWeight n ≤ 10 * (n:ℝ) * 2^n
    unfold highWeight
    nlinarith

private theorem coarsen {q : ℝ} (hq : 0 ≤ q) {ell N : ℕ} (h : traceDeviation q ell N) :
    (q - ell) * (q - ell - 1) - (3:ℝ)^ell * N ≤
    ((ell:ℝ) * 2^ell)^2 * q + 10 * ((ell:ℝ) * 2^ell) * (q + q * √q) := by
  have hb := (abs_sub_le_iff.mp h).2
  have hs : highWeight ell * (q + q * √q) ≤ (10 * ell * 2^ell) * (q + q * √q) :=
    mul_le_mul_of_nonneg_right (highWeight_le ell) (by positivity)
  have h42 : (4:ℝ)^ell = ((2:ℝ)^ell)^2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  have h42' : 1 ≤ (4:ℝ)^ell := one_le_pow_of_one_le (by norm_num) _
  have hn : (0:ℝ) ≤ ell := by positivity
  have hf : (ell:ℝ) * (ell - 1) * (4^ell - 1) ≤ ((ell:ℝ) * 2^ell)^2 := by
    calc
      _ ≤ (ell:ℝ) * ell * (4^ell - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hn) (by linarith)
      _ ≤ (ell:ℝ) * ell * 4^ell :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by rw [h42]; ring
  linarith [mul_le_mul_of_nonneg_right hf hq]

/-- A finite positivity test from the trace bound; no asymptotic notation. -/
theorem count_pos_of_small {q : ℝ} {ell N : ℕ} (hq : 16 ≤ q)
    (hsmall : 32 * ((ell:ℝ) * 2^ell) ≤ √q) (h : traceDeviation q ell N) : 0 < N := by
  by_contra! hN
  have hz : N = 0 := by omega
  subst N
  let t : ℝ := (ell:ℝ) * 2^ell
  have hr : (√q)^2 = q := sq_sqrt (by linarith)
  have hr1 : 1 ≤ √q := by
    by_contra! ha
    nlinarith [sq_nonneg (√q - 1), mul_nonneg (sqrt_nonneg q) (sub_nonneg.mpr ha.le)]
  have hrq : √q ≤ q := by nlinarith [mul_nonneg (sqrt_nonneg q) (sub_nonneg.mpr hr1)]
  have hel : (ell:ℝ) ≤ t := by
    dsimp [t]
    exact le_mul_of_one_le_right (by positivity) (one_le_pow_of_one_le (by norm_num) _)
  change 32 * t ≤ √q at hsmall
  have hp1 : 7*q/8 ≤ q - ell := by linarith
  have hp2 : 7*q/8 ≤ q - ell - 1 := by linarith
  have hmain := mul_le_mul hp1 hp2 (by linarith : 0 ≤ 7*q/8) (by linarith)
  have ht2 : t^2 ≤ q/1024 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (show 0 ≤ √q+32*t by positivity)]
  have hw : t * √q ≤ q/32 := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (sqrt_nonneg q)]
  have hb := coarsen (by linarith : 0 ≤ q) h
  simp only [Nat.cast_zero, mul_zero, sub_zero] at hb
  change (q - ell) * (q - ell - 1) ≤ t^2 * q + 10*t*(q + q * √q) at hb
  have htq : t ≤ q / 32 := by linarith
  nlinarith [mul_le_mul_of_nonneg_right ht2 (show 0 ≤ q by linarith),
    mul_le_mul_of_nonneg_right hw (show 0 ≤ q by linarith),
    mul_le_mul_of_nonneg_right htq (show 0 ≤ q by linarith),
    mul_pos (show 0 < q by linarith) (show 0 < q by linarith)]

private theorem log_four_lower : 1 ≤ log 4 := by
  have ha := log_le_sub_one_of_pos (show (0:ℝ) < 2⁻¹ by norm_num)
  rw [log_inv] at ha
  rw [show (4:ℝ) = 2^2 by norm_num, log_pow]
  norm_num at ha ⊢
  linarith

/-- From (12.1) and a zero count one gets the manuscript's strict lower bound
already when q ≥ 16. This implication does not assume a limiting formula. -/
theorem cubic_lower_of_trace (q : ℝ) (ell : ℕ) (hq : 16 ≤ q)
    (h : traceDeviation q ell 0) :
    (log q - 2 * log (log q)) / log 4 - 5 < (ell:ℝ) := by
  by_contra! hs
  have h4 := log_four_lower
  have hL : 1 ≤ log q := h4.trans (log_le_log (by norm_num) (by linarith))
  have hlL : 0 ≤ log (log q) := log_nonneg hL
  have hB : ((ell:ℝ)+5) * log 4 ≤ log q - 2*log (log q) :=
    (le_div_iff (by linarith : 0 < log 4)).mp (by linarith)
  have helL : (ell:ℝ) ≤ log q := by
    nlinarith [mul_le_mul_of_nonneg_left h4 (show 0 ≤ (ell:ℝ)+5 by positivity)]
  have hlog4 : log 4 = 2 * log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow]; norm_num
  have hlog32 : log 32 = 5 * log 2 := by
    rw [show (32:ℝ) = 2^5 by norm_num, log_pow]; norm_num
  have ht : 32 * (log q * 2^ell) ≤ √q := by
    apply (log_le_log_iff (by positivity) (sqrt_pos.2 (by linarith))).mp
    rw [log_mul (by norm_num) (by positivity), log_mul (by linarith) (by positivity),
      log_pow, log_sqrt (by linarith), hlog32]
    rw [hlog4] at hB
    linarith
  have ht' : 32 * ((ell:ℝ) * 2^ell) ≤ √q :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right helL (by positivity)) (by norm_num)).trans ht
  exact (Nat.lt_irrefl 0) (count_pos_of_small hq ht' h)

/-- The wild fixed-slope estimate of §18, before passing to logarithms. -/
def fixedSlopeDeviation (q : ℝ) (ell N : ℕ) : Prop :=
  |(3:ℝ)^ell * N - (q - ell)| ≤ (2 * (ell:ℝ) - 1) * (4^ell - 1) * √q

private theorem log_sixteen_lower : 7 / 3 ≤ log 16 := by
  have ha := log_le_sub_one_of_pos (show (0:ℝ) < 3/4 by norm_num)
  have hb := log_le_sub_one_of_pos (show (0:ℝ) < 2/3 by norm_num)
  have hc := log_mul (show (3/4:ℝ) ≠ 0 by norm_num) (show (2/3:ℝ) ≠ 0 by norm_num)
  rw [show (3/4:ℝ) * (2/3) = 2⁻¹ by norm_num, log_inv] at hc
  rw [show (16:ℝ) = 2^4 by norm_num, log_pow]
  norm_num
  linarith

/-- Explicit second-order consequence of the trace input used in characteristic two.
The coefficient and the absence of an additive loss hold uniformly for q ≥ 16. -/
theorem fixedSlope_lower_of_trace (q : ℝ) (ell : ℕ) (hq : 16 ≤ q)
    (h : fixedSlopeDeviation q ell 0) :
    (log q - 2 * log (log q)) / log 16 < (ell:ℝ) := by
  by_contra! hs
  have h16 := log_sixteen_lower
  have hL : 1 ≤ log q := log_four_lower.trans (log_le_log (by norm_num) (by linarith))
  have hlL := log_nonneg hL
  have hB := (le_div_iff (by linarith : 0 < log 16)).mp hs
  have hr : (√q)^2 = q := sq_sqrt (by linarith)
  have hr4 : 4 ≤ √q := by
    by_contra! ha
    nlinarith [mul_pos (sub_pos.mpr ha) (show 0 < 4+√q by positivity)]
  have hrq : 4 * √q ≤ q := by nlinarith [mul_nonneg (sqrt_nonneg q) (sub_nonneg.mpr hr4)]
  have hlog16 : log 16 = 2 * log 4 := by
    rw [show (16:ℝ) = 4^2 by norm_num, log_pow]; norm_num
  have hsmall : log q * (4:ℝ)^ell ≤ √q := by
    apply (log_le_log_iff (by positivity) (sqrt_pos.2 (by linarith))).mp
    rw [log_mul (by linarith) (by positivity), log_pow, log_sqrt (by linarith)]
    rw [hlog16] at hB
    linarith
  let t : ℝ := (ell:ℝ) * 4^ell
  have ha : (1:ℝ) ≤ (4:ℝ)^ell := one_le_pow_of_one_le (by norm_num) _
  have hn : 0 ≤ (ell:ℝ) := by positivity
  have ht : 7*t ≤ 3*√q := by
    have hel : (7/3:ℝ) * ell ≤ log q := by nlinarith [mul_le_mul_of_nonneg_right h16 hn]
    have hh := mul_le_mul_of_nonneg_right hel (show 0 ≤ (4:ℝ)^ell by positivity)
    dsimp [t]
    linarith
  have hel : (ell:ℝ) ≤ t := le_mul_of_one_le_right hn ha
  have he : (2 * (ell:ℝ) - 1) * (4^ell - 1) ≤ 2*t := by dsimp [t]; nlinarith
  have hb := (abs_sub_le_iff.mp h).2
  simp only [Nat.cast_zero, mul_zero, sub_zero] at hb
  have herror : 2*t*√q ≤ 6*q/7 := by
    linarith only [mul_le_mul_of_nonneg_right ht (sqrt_nonneg q), hr]
  have hlen : (ell:ℝ) ≤ 3*q/28 := by linarith only [hel, ht, hrq]
  linarith only [hb, mul_le_mul_of_nonneg_right he (sqrt_nonneg q), herror, hlen, hq]

/-- A numerical Hasse–Weil test, also valid with nontrivial constants in the original
splitting field. A geometrically connected twist of genus at most ell*C*D^ell
then has more rational points than all fibers over ell+2 excluded values contain.
The twist construction and the genus estimate enter separately. -/
theorem twist_point_threshold {q D C g : ℝ} {ell : ℕ}
    (hq : 16 ≤ q) (hD : 2 ≤ D) (hC : 1 ≤ C)
    (hg : g ≤ (ell:ℝ) * C * D^ell)
    (hs : (ell:ℝ) ≤ (log q - 2*log (log q)) / (2*log D) - log (16*C)/log D) :
    ((ell:ℝ)+2)*D^ell < q+1-2*g*√q := by
  have hd := log_pos (show 1 < D by linarith)
  have h2 : 1 ≤ 2*log D := by
    have h4 := log_four_lower
    rw [show (4:ℝ) = 2^2 by norm_num, log_pow] at h4
    norm_num at h4
    linarith [log_le_log (by norm_num : (0:ℝ)<2) hD]
  have hL : 1 ≤ log q := log_four_lower.trans (log_le_log (by norm_num) (by linarith))
  have hlogC : 0 ≤ log (16*C) := log_nonneg (by linarith)
  have hB : (ell:ℝ) * (2*log D) + 2*log (16*C) ≤ log q - 2*log (log q) := by
    have hb := (le_div_iff (by linarith only [hd] : 0 < 2*log D)).mp
      (le_sub_iff_add_le.mp hs)
    calc
      _ = ((ell:ℝ) + log (16*C)/log D) * (2*log D) := by field_simp; ring
      _ ≤ _ := hb
  have hel : (ell:ℝ) ≤ log q := by
    nlinarith only [hB, hlogC, log_nonneg hL,
      mul_le_mul_of_nonneg_left h2 (show 0 ≤ (ell:ℝ) by positivity)]
  have hsmall : (16*C)*(log q * D^ell) ≤ √q := by
    apply (log_le_log_iff (by positivity) (sqrt_pos.2 (by linarith))).mp
    rw [log_mul (x := 16*C) (by positivity) (by positivity),
      log_mul (x := log q) (by linarith only [hL]) (by positivity),
      log_pow, log_sqrt (by linarith only [hq])]
    linarith only [hB]
  have hr := sq_sqrt (show 0 ≤ q by linarith)
  have hr1 : 1 ≤ √q := one_le_sqrt.mpr (by linarith only [hq])
  have hrq : √q ≤ q := by linarith only [hr, mul_nonneg (sqrt_nonneg q) (sub_nonneg.mpr hr1)]
  have ha : 0 ≤ D^ell := by positivity
  let u := log q * D^ell
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have htu : (ell:ℝ)*D^ell ≤ u := mul_le_mul_of_nonneg_right hel ha
  have hau : D^ell ≤ u := le_mul_of_one_le_left ha hL
  change 16*C*u ≤ √q at hsmall
  have hus : u ≤ q/16 := by linarith only [hsmall, hrq, mul_le_mul_of_nonneg_right hC hu]
  have hrem : ((ell:ℝ)+2)*D^ell ≤ 3*q/16 := by linarith only [hus, htu, hau]
  have hgen : 16*g ≤ √q := by linarith only [hg, mul_le_mul_of_nonneg_left htu (show 0 ≤ C by linarith), hsmall]
  linarith only [hr, hq, hrem, mul_le_mul_of_nonneg_right hgen (sqrt_nonneg q)]

end BlockingCurves.CubicAsymptotics
