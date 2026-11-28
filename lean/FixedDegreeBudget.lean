import CubicAsymptotics
import Mathlib.Data.Complex.ExponentialBounds

/-! An explicit logarithmic window for the root-tower genus and the number
of points above the discarded branch values. The degree and translate
count occur as variables, so the estimate can be applied to growing sets. -/
namespace BlockingCurves.FixedDegreeBudget
open Real

/-- Positivity on the twist from the numerical genus and deleted-fibre bounds.
Here D bounds the order of a single geometric group and d the map degree. -/
theorem growing_window {q d D g b H : ℝ} {ell : ℕ}
    (hd : 2 ≤ d) (hD : 2 ≤ D) (hL : 1 ≤ log q) (hq : 0 < q)
    (hg : 2*g ≤ ell*(d-1)*H) (hH : H ≤ D^ell) (hH0 : 0 ≤ H)
    (hb : b ≤ 1+d*ell)
    (window : (ell:ℝ)*log D ≤ log q/2-log (log q)-log (4*(d+1))) :
    b*H < q+1-2*g*sqrt q := by
  have q1 : 1 ≤ q := by
    by_contra! he
    have := log_neg hq he
    linarith
  have r1 : 1 ≤ sqrt q := by simpa using sqrt_le_sqrt q1
  have rr := sq_sqrt hq.le
  have ld : (1:ℝ)/2 ≤ log D := by
    have h := log_le_log (by norm_num : (0:ℝ)<2) hD
    exact le_trans (by norm_num : (1:ℝ)/2 ≤ 0.6931471803) (Real.log_two_gt_d9.le.trans h)
  have lq : 0 < log q := by linarith
  have la : 0 ≤ log (4*(d+1)) := log_nonneg (by linarith)
  have ell0 : 0 ≤ (ell:ℝ) := by positivity
  have ellL : (ell:ℝ) ≤ log q := by
    linarith only [window,la,log_nonneg hL,mul_le_mul_of_nonneg_left ld ell0]
  have coeff : 0 < 4*(d+1) := by linarith
  have dp : 0 < D^ell := pow_pos (by linarith) _
  have cost : 4*(d+1)*log q*D^ell ≤ sqrt q := by
    apply (log_le_log_iff (by positivity) (sqrt_pos.2 hq)).1
    rw [log_mul (mul_pos coeff lq).ne' dp.ne',log_mul coeff.ne' lq.ne',
      log_pow,log_sqrt hq.le]
    linarith
  have prod : 4*(d+1)*log q*H ≤ sqrt q :=
    (mul_le_mul_of_nonneg_left hH (mul_pos coeff lq).le).trans cost
  have genus : 2*g ≤ (d+1)*log q*H := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ hH0
    nlinarith only [mul_le_mul_of_nonneg_left ellL (by linarith : 0 ≤ d-1),hL]
  have removed : b*H ≤ (d+1)*log q*H := by
    apply mul_le_mul_of_nonneg_right _ hH0
    nlinarith only [hb,mul_le_mul_of_nonneg_left ellL (by linarith : 0 ≤ d),hL]
  have quarter : (d+1)*log q*H ≤ sqrt q/4 := by linarith only [prod]
  have gg := mul_le_mul_of_nonneg_right (genus.trans quarter) (sqrt_nonneg q)
  have rle : sqrt q ≤ q := by nlinarith only [rr,mul_nonneg (sqrt_nonneg q) (sub_nonneg.mpr r1)]
  nlinarith only [removed.trans quarter,gg,rr,rle,hq]

end BlockingCurves.FixedDegreeBudget
