import NormPencilField
import PencilAsymptotic

/-! Single-point sampling for the mixed monomial. Raising the fibre equation
to the m-th power replaces its large exponent by a polynomial of degree sm,
uniformly for horizontal and nonhorizontal lines. -/

namespace BlockingCurves.PhasePointCover

open Finset Polynomial PencilSampling NormPencil
open scoped BigOperators Polynomial

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
attribute [local instance] Classical.propDecidable

/-- If md=k+q−1 and k>m>0, every intercept fibre has at most k points. -/
theorem mixed_fibre {d m k : ℕ} (hm : 0 < m) (hk : m < k)
    (exponents : d*m=k+(Fintype.card E-1)) (a b y : E) :
    (univ.filter (fun x : E => x^d-a*x-b=y)).card ≤ k := by
  classical
  let A : E[X] := C a*X + C (b+y)
  let P : E[X] := X^k - A^m
  have hdA : A.natDegree ≤ 1 := by dsimp [A]; compute_degree
  have hdAm : (A^m).natDegree ≤ m := by
    rw [natDegree_pow]
    nlinarith only [Nat.mul_le_mul_left m hdA]
  have hdP : P.natDegree=k := by
    change (X^k - A^m : E[X]).natDegree = k
    have lt : (A^m).natDegree < (X^k : E[X]).natDegree := by rw [natDegree_X_pow]; exact hdAm.trans_lt hk
    rw [natDegree_sub_eq_left_of_natDegree_lt lt,natDegree_X_pow]
  have hP : P ≠ 0 := fun h => by simp [h] at hdP; omega
  rw [← hdP]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  have h := (Finset.mem_filter.mp (show x ∈ univ.filter (fun x : E => x^d-a*x-b=y) from hx)).2
  have hval : x^d = a*x+(b+y) := by linear_combination h
  have poweq : (x^d)^m=x^k := by
    rw [← pow_mul,exponents,pow_add]
    by_cases zero : x=0
    · simp [zero,zero_pow (by omega : k≠0)]
    · rw [FiniteField.pow_card_sub_one_eq_one _ zero,mul_one]
  apply (Polynomial.mem_roots hP).2
  simp only [P,A,Polynomial.IsRoot,eval_sub,eval_pow,eval_X,eval_add,eval_mul,eval_C]
  rw [← hval,poweq,sub_self]

/-- Uniform single-point projective cover for all fields and all exponent
pairs satisfying md=k+q−1. -/
theorem reduced_power_upper {d m k : ℕ} (hd : 2 ≤ d) (hm : 0 < m) (hk : m < k)
    (exponents : d*m=k+(Fintype.card E-1)) :
    ∃ S : Finset E, ProjectiveBlocks d (S : Set E) ∧
      (S.card:ℝ) ≤ 2*k*Real.log (2*Fintype.card E)+1 := by
  classical
  let q := Fintype.card E
  let r := (1:ℝ)/k
  let N := ⌊(q:ℝ)*Real.exp (-r)⌋₊
  have hq : (0:ℝ)<q := Nat.cast_pos.mpr Fintype.card_pos
  have hk0 : (0:ℝ)<k := Nat.cast_pos.mpr (lt_trans hm hk)
  have hr : 0 < r := one_div_pos.mpr hk0
  have bound : (N:ℝ) ≤ q*Real.exp (-r) := Nat.floor_le (by positivity)
  have miss (l : Lines E) : (missed d l).card ≤ N := by
    let a := (PencilSampling.coordinates l).1
    let b := (PencilSampling.coordinates l).2
    let f (x:E) := x^d-a*x-b
    let I := univ.image f
    have kI : q ≤ k*I.card := by
      simpa only [card_univ] using (Finset.card_le_mul_card_image (f := f) univ k
        (fun y _ => mixed_fibre hm hk exponents a b y))
    have om : missed d l = Iᶜ := by
      ext y
      simp [missed,Hits,I,f,a,b]
    have cnt : (missed d l).card + I.card = q := by
      rw [om,Finset.card_compl,Nat.sub_add_cancel (Finset.card_le_univ I)]
    have kR : (q:ℝ) ≤ k*(I.card:ℝ) := by exact_mod_cast kI
    have cntR : ((missed d l).card:ℝ) + (I.card:ℝ) = q := by exact_mod_cast cnt
    have fir : ((missed d l).card:ℝ) ≤ q*(1-r) := by
      have share : (q:ℝ)/k ≤ I.card := (div_le_iff hk0).2 (by simpa [mul_comm] using kR)
      dsimp [r]; rw [mul_sub,mul_one,mul_one_div]; linarith
    apply Nat.le_floor
    exact fir.trans (mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (-r)]) hq.le)
  obtain ⟨S,hS,card⟩ := projective_split_upper (F := E) (ε := 0) hd hr hr le_rfl
    (by simpa using mul_nonneg hr.le (Real.sqrt_nonneg (Fintype.card E)))
    (fun b => miss (.inl b)) (fun l => miss (.inr l)) bound (by simpa using bound)
  refine ⟨S,hS,card.trans ?_⟩
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt (Fintype.one_lt_card (α := E))))
  change sampleCutoff q (1/2) (1/(k:ℝ)) (1/(k:ℝ)) 0 + 1 ≤ 2*k*Real.log (2*q)+1
  simp only [sampleCutoff, Real.log_inv, Real.log_div one_ne_zero (by norm_num : (2:ℝ)≠0),
    Real.log_one, Real.log_mul (by norm_num : (2:ℝ)≠0) hq.ne',zero_sub,sub_neg_eq_add,
    zero_div,mul_zero,add_zero,one_div,div_inv_eq_mul]
  apply add_le_add_right
  apply max_le
  · nlinarith only [mul_nonneg hlog hk0.le]
  · ring_nf; rfl

/-- For every base-field size, one obtains an explicit projective cover by
at most 2ms log(2q)+1 single point shifts. -/
theorem point_upper {m n : ℕ} (hm : 2 ≤ m) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) :
    ∃ S : Finset E, ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S:Set E) ∧
      (S.card:ℝ) ≤ 2*m*Fintype.card F*Real.log (2*Fintype.card E)+1 := by
  have hs : 1<Fintype.card F := Fintype.one_lt_card
  have hdvd : m ∣ Fintype.card E-1 := by
    rw [size,←normExponent_mul (Fintype.card F) n hs.le,Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right divides _
  have ex : (Fintype.card F+(Fintype.card E-1)/m)*m =
      m*Fintype.card F+(Fintype.card E-1) := by rw [add_mul,Nat.div_mul_cancel hdvd,mul_comm (Fintype.card F)]
  have hk : m < m*Fintype.card F := by nlinarith only [Nat.mul_lt_mul_of_pos_left hs (by omega : 0<m)]
  have hd : 2 ≤ Fintype.card F+(Fintype.card E-1)/m := le_trans hs (Nat.le_add_right _ _)
  obtain ⟨S,hS,h⟩ := reduced_power_upper hd (by omega : 0<m) hk ex
  refine ⟨S,hS,?_⟩
  simpa only [Nat.cast_mul,mul_assoc] using h

/-- This explicit C(m) bounds the remaining finite range of base sizes,
uniformly in the extension dimension. -/
theorem small_base_upper {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) (small : Fintype.card F < (1+2*m^2)^2) :
    ∃ S : Finset E, ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S:Set E) ∧
      S.card ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  obtain ⟨S,hS,h⟩ := point_upper hm divides size
  refine ⟨S,hS,?_⟩
  have hs : (1:ℝ) ≤ Fintype.card F := by exact_mod_cast (Nat.le_of_lt (Fintype.one_lt_card (α := F)))
  have nn : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hg : (Fintype.card F:ℝ) ≤ (1+2*(m:ℝ)^2)^2 := by exact_mod_cast small.le
  have hlog : Real.log (2*(Fintype.card E:ℝ)) ≤ n*(1+(1+2*(m:ℝ)^2)^2) := by
    rw [size,Nat.cast_pow,Real.log_mul (by norm_num) (pow_pos (by linarith) n).ne', Real.log_pow]
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hbase := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<Fintype.card F)
    nlinarith only [h2,nn,mul_le_mul_of_nonneg_left (hbase.trans (by linarith : (Fintype.card F:ℝ)-1 ≤ (1+2*(m:ℝ)^2)^2)) (by positivity : (0:ℝ) ≤ n)]
  have hs1 : (1:ℝ) ≤ n*(Fintype.card F:ℝ) := nn.trans (by simpa using mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ n))
  have finalR : (S.card:ℝ) ≤ (2*(m:ℝ)*(1+(1+2*(m:ℝ)^2)^2)+1)*n*Fintype.card F := by
    nlinarith only [h,hs1,mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 2*m*Fintype.card F)]
  exact_mod_cast finalR

end BlockingCurves.PhasePointCover
