import PencilSampling

/-! Explicit two-rate sampling with a square-root value-set error. -/
namespace BlockingCurves.PencilSampling
open Finset Real

/-- Required sample size at real residual budget z. The exponent loss from
the nonzero slopes is bounded by a constant independent of both q and k. -/
noncomputable def sampleCutoff (q z μ ν ε : ℝ) : ℝ :=
  max ((log q - log z + log 2)/μ) ((2*log q - log z + log 2)/ν + 12*ε/ν^2)

private theorem one_moment {q z M u : ℝ} {k e : ℕ}
    (hq : 0 < q) (hz : 0 < z) (hM0 : 0 ≤ M) (hM : M ≤ q * exp (-u))
    (hk : (e:ℝ)*log q - log z + log 2 ≤ (k:ℝ)*u) :
    q^e * M^k ≤ q^k * (z/2) := by
  have ht : q^e * exp (-u)^k ≤ z/2 := by
    apply (log_le_log_iff (by positivity) (by positivity)).mp
    rw [log_mul (by positivity) (by positivity), log_pow, log_pow, log_exp,
      log_div hz.ne' (by norm_num)]
    linarith only [hk]
  calc
    _ ≤ q^e * (q*exp (-u))^k := by gcongr
    _ = q^k * (q^e*exp (-u)^k) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)

/-- A loss of ε/√q in the exponent contributes at most 12ε/ν² to the
sampling threshold. The bound holds simultaneously for growing k and q. -/
theorem two_rate_size {q z H N μ ν ε : ℝ} (hq : 2 ≤ q)
    (hz : 1/2 ≤ z) (hμ : 0 < μ) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hsmall : 2*ε ≤ ν*sqrt q)
    (hH0 : 0 ≤ H) (hN0 : 0 ≤ N)
    (hH : H ≤ q*exp (-μ)) (hN : N ≤ q*exp (-(ν-ε/sqrt q))) {k : ℕ}
    (hk : sampleCutoff q z μ ν ε ≤ k) :
    q*H^k + q^2*N^k ≤ q^k*z := by
  have hq0 : 0 < q := by linarith
  have hz0 : 0 < z := by linarith
  have hs : 1 ≤ sqrt q := by
    rw [Real.le_sqrt (by norm_num) hq0.le]
    linarith
  have hs0 : 0 < sqrt q := by linarith
  have hlogq : log q ≤ 2*sqrt q := by
    have h := log_le_sub_one_of_pos hs0
    rw [log_sqrt hq0.le] at h
    linarith
  have hzlog : -log 2 ≤ log z := by
    have h := log_le_log (by norm_num : (0:ℝ) < 1/2) hz
    simpa [one_div] using h
  have hlog2 := log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  let A := 2*log q - log z + log 2
  have hA : A ≤ 6*sqrt q := by dsimp [A]; linarith
  have hdrop : ε/sqrt q ≤ ν/2 := (div_le_iff hs0).mpr (by linarith)
  have hrate : 0 < ν-ε/sqrt q := by linarith
  have hAerr : A*(ε/sqrt q) ≤ 6*ε := by
    calc
      _ ≤ (6*sqrt q)*(ε/sqrt q) := mul_le_mul_of_nonneg_right hA (by positivity)
      _ = _ := by field_simp; ring
  have herr : (12*ε/ν^2)*(ν/2) ≤ (12*ε/ν^2)*(ν-ε/sqrt q) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hcut : A ≤ (A/ν+12*ε/ν^2)*(ν-ε/sqrt q) := by
    have h1 := (div_le_div_right hν).mpr hAerr
    have h2 : (12*ε/ν^2)*(ν/2) = 6*ε/ν := by field_simp; ring
    have h3 : (A/ν)*(ν-ε/sqrt q) = A - A*(ε/sqrt q)/ν := by field_simp; ring
    rw [h2] at herr
    rw [add_mul,h3]
    linarith only [h1,herr]
  have hmax := max_le_iff.mp hk
  have hK0 := (div_le_iff hμ).mp hmax.1
  have hK1 := hcut.trans (mul_le_mul_of_nonneg_right hmax.2 hrate.le)
  have h0 := one_moment (e := 1) hq0 hz0 hH0 hH (by simpa using hK0)
  have h1 := one_moment (e := 2) hq0 hz0 hN0 hN (by simpa [A] using hK1)
  simp only [pow_one] at h0
  linarith only [h0,h1]

/-- Converts an additive error in the missing fraction δ+C/√q into the
exponent loss used by the finite sampling estimate. -/
theorem additive_miss_rate {q δ C : ℝ} (hq : 0 < q) (hδ : 0 < δ) :
    δ + C/sqrt q ≤ exp (-(log (1/δ) - (C/δ)/sqrt q)) := by
  have h := mul_le_mul_of_nonneg_left (add_one_le_exp ((C/δ)/sqrt q)) hδ.le
  rw [neg_sub, sub_eq_add_neg, exp_add, one_div, log_inv, neg_neg, exp_log hδ]
  have he : δ * ((C/δ)/sqrt q+1) = δ+C/sqrt q := by field_simp; ring
  linarith only [h,he,mul_comm δ (exp ((C/δ)/sqrt q)) |>.le,
    mul_comm δ (exp ((C/δ)/sqrt q)) |>.ge]


variable {F : Type*} [Field F] [Fintype F]

private theorem finite_threshold {k t H N : ℕ} {z μ ν ε : ℝ}
    (hz : 1/2 ≤ z) (ht : z < (t:ℝ)+1)
    (hμ : 0 < μ) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hsmall : 2*ε ≤ ν*sqrt (Fintype.card F))
    (hH : (H:ℝ) ≤ Fintype.card F*exp (-μ))
    (hN : (N:ℝ) ≤ Fintype.card F*exp (-(ν-ε/sqrt (Fintype.card F))))
    (hk : sampleCutoff (Fintype.card F) z μ ν ε ≤ k) :
    Fintype.card F*H^k + Fintype.card F*(Fintype.card F-1)*N^k <
      Fintype.card F^k*(t+1) := by
  let q := Fintype.card F
  have hq : (2:ℝ) ≤ q := by exact_mod_cast Fintype.one_lt_card (α := F)
  have h := two_rate_size hq hz hμ hν hε hsmall (Nat.cast_nonneg H)
    (Nat.cast_nonneg N) hH hN hk
  have hp : 0 < (q:ℝ)^k := by positivity
  have h' : (q:ℝ)*H^k+(q:ℝ)^2*N^k < (q:ℝ)^k*((t:ℝ)+1) :=
    h.trans_lt (mul_lt_mul_of_pos_left ht hp)
  have h'' : q*H^k+q^2*N^k < q^k*(t+1) := by exact_mod_cast h'
  have hl : q*(q-1) ≤ q^2 := by
    rw [pow_two]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _).trans_lt h''

private theorem cutoff_nonneg {q z μ ν ε : ℝ}
    (hz : 0 < z) (hzq : z ≤ q) (hμ : 0 < μ) :
    0 ≤ sampleCutoff q z μ ν ε := by
  apply le_trans _ (le_max_left _ _)
  apply div_nonneg _ hμ.le
  linarith only [log_le_log hz hzq, log_nonneg (by norm_num : (1:ℝ) ≤ 2)]

/-- No repair hypothesis for the leading-order bound. With z=1/2, the two
leading coefficients are 1/μ and 2/ν. -/
theorem projective_split_upper {d H N : ℕ} (hd : 2 ≤ d) {μ ν ε : ℝ}
    (hμ : 0 < μ) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hsmall : 2*ε ≤ ν*sqrt (Fintype.card F))
    (hh : ∀ b : F, (missed d (.inl b : Lines F)).card ≤ H)
    (hn : ∀ l : Fˣ × F, (missed d (.inr l : Lines F)).card ≤ N)
    (hH : (H:ℝ) ≤ Fintype.card F*exp (-μ))
    (hN : (N:ℝ) ≤ Fintype.card F*exp (-(ν-ε/sqrt (Fintype.card F)))) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card : ℝ) ≤ sampleCutoff (Fintype.card F) (1/2) μ ν ε + 1 := by
  let a := sampleCutoff (Fintype.card F) (1/2) μ ν ε
  let k := ⌈a⌉₊
  have hq : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.one_lt_card (α := F)
  have hzq : (1/2:ℝ) ≤ Fintype.card F := by linarith
  have h := finite_threshold (F := F) (k := k) (t := 0) le_rfl (by norm_num)
    hμ hν hε hsmall hH hN (Nat.le_ceil a)
  obtain ⟨S,hs,hb⟩ := projective_first_moment hd k H N hh hn (by simpa using h)
  exact ⟨S,hb,(show (S.card:ℝ) ≤ k by exact_mod_cast hs).trans
    (Nat.ceil_lt_add_one (cutoff_nonneg (by norm_num) hzq hμ)).le⟩

/-- Explicit log-log upper bound. A common repair for floor(c log q) lines
and the one-line value-set bounds are the two geometric inputs. -/
theorem projective_split_loglog {d H N : ℕ} (hd : 2 ≤ d) {c μ ν ε : ℝ}
    (hc : 0 < c) (hz : 1/2 ≤ c*log (Fintype.card F))
    (hzq : c*log (Fintype.card F) ≤ Fintype.card F)
    (hμ : 0 < μ) (hν : 0 < ν) (hε : 0 ≤ ε)
    (hsmall : 2*ε ≤ ν*sqrt (Fintype.card F))
    (hh : ∀ b : F, (missed d (.inl b : Lines F)).card ≤ H)
    (hn : ∀ l : Fˣ × F, (missed d (.inr l : Lines F)).card ≤ N)
    (hH : (H:ℝ) ≤ Fintype.card F*exp (-μ))
    (hN : (N:ℝ) ≤ Fintype.card F*exp (-(ν-ε/sqrt (Fintype.card F))))
    (hcommon : CommonHit F d ⌊c*log (Fintype.card F)⌋₊) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ max
        ((log (Fintype.card F) - log (log (Fintype.card F)) - log c + log 2)/μ)
        ((2*log (Fintype.card F) - log (log (Fintype.card F)) - log c + log 2)/ν
          + 12*ε/ν^2) + 2 := by
  let q : ℝ := Fintype.card F
  let z := c*log q
  let a := sampleCutoff q z μ ν ε
  let k := ⌈a⌉₊
  have hq : (2:ℝ) ≤ q := by
    dsimp [q]; exact_mod_cast (show 2 ≤ Fintype.card F from Fintype.one_lt_card)
  have hL := log_pos (by linarith : 1 < q)
  have hz0 : 0 < z := mul_pos hc hL
  have h := finite_threshold (F := F) (k := k) (t := ⌊z⌋₊) hz
    (Nat.lt_floor_add_one z) hμ hν hε hsmall hH hN (Nat.le_ceil a)
  obtain ⟨S,hs,hb⟩ := projective_after_repair hd k _ H N hh hn h hcommon
  have hk : (k:ℝ) < a+1 := Nat.ceil_lt_add_one (cutoff_nonneg hz0 hzq hμ)
  have hs' : (S.card:ℝ) ≤ (k:ℝ)+1 := by exact_mod_cast hs
  refine ⟨S,hb,?_⟩
  have ha : (S.card:ℝ) ≤ a+2 := by linarith only [hk,hs']
  dsimp [a,z,sampleCutoff] at ha
  rw [log_mul hc.ne' hL.ne'] at ha
  simpa only [sub_add_eq_sub_sub, sub_right_comm _ (log c)] using ha


end BlockingCurves.PencilSampling
