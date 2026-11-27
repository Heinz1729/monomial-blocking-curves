import PhaseCharacterBudget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.NumberTheory.LegendreSymbol.MulCharacter

/-! Orthogonality of simultaneous multiplicative character conditions. The
point-count error after normalization is at most the worst nonprincipal sum,
uniformly in the number of coordinates. -/

namespace BlockingCurves.PhaseCharacter

open Finset
open scoped BigOperators

variable {K : Type*} {m M : ℕ}

/-- The sum over one cyclic character coordinate detects its target. -/
theorem one_coordinate (z : ℂ) (hz : z^m = 1) :
    (∑ j : Fin m, z^(j:ℕ)) = if z=1 then (m:ℂ) else 0 := by
  classical
  by_cases h : z=1
  · simp [h]
  · rw [Fin.sum_univ_eq_sum_range (fun j => z^j), geom_sum_eq h, hz]
    simp [h]

/-- The Fourier sum for one exponent vector on a finite set of parameters.
The input values are the actual character values divided by their prescribed targets. -/
noncomputable def patternSum (D : Finset K) (z : Fin M → K → ℂ) (e : Fin M → Fin m) : ℂ :=
  ∑ x ∈ D, ∏ i, z i x ^ (e i : ℕ)

noncomputable def patternCount (D : Finset K) (z : Fin M → K → ℂ) : ℕ :=
  open Classical in (D.filter (fun x => ∀ i, z i x = 1)).card

/-- Expanding every cyclic orthogonality relation and interchanging the two
finite sums gives the exact unnormalized pattern count. -/
theorem pattern_expansion (D : Finset K) (z : Fin M → K → ℂ)
    (roots : ∀ x ∈ D, ∀ i, z i x ^ m = 1) :
    (∑ e : Fin M → Fin m, patternSum D z e) = (m:ℂ)^M * patternCount D z := by
  classical
  unfold patternSum
  rw [Finset.sum_comm]
  have single (x : K) (hx : x ∈ D) :
      (∑ e : Fin M → Fin m, ∏ i, z i x ^ (e i : ℕ)) =
        (m:ℂ)^M * (if ∀ i, z i x = 1 then 1 else 0) := by
    have eq := (Finset.prod_univ_sum (fun _ : Fin M => (univ : Finset (Fin m)))
      (fun i (j : Fin m) => z i x ^ (j:ℕ))).symm
    rw [Fintype.piFinset_univ] at eq
    rw [eq]
    simp_rw [one_coordinate _ (roots x hx _)]
    by_cases h : ∀ i, z i x = 1
    · simp [h]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      rw [Finset.prod_eq_zero (f := fun j : Fin M => if z j x = 1 then (m : ℂ) else 0) (Finset.mem_univ i) (if_neg hi)]
      simp [h]
  simp_rw [Finset.sum_congr rfl single, ← Finset.mul_sum]
  simp [patternCount]

/-- A bound for each nonprincipal sum supplies the same bound for the absolute
error of the normalized count, for all M including zero. The m^M possible
terms are canceled by the normalization rather than charged to the error. -/
theorem pattern_discrepancy [NeZero m] (D : Finset K) (z : Fin M → K → ℂ)
    (roots : ∀ x ∈ D, ∀ i, z i x ^ m = 1) {W : ℝ} (hW : 0 ≤ W)
    (nonprincipal : ∀ e : Fin M → Fin m, e ≠ 0 → ‖patternSum D z e‖ ≤ W) :
    |(patternCount D z : ℝ) - D.card/(m:ℝ)^M| ≤ W := by
  classical
  let I := (Finset.univ : Finset (Fin M → Fin m)).erase 0
  have hm : m ≠ 0 := NeZero.ne m
  have hmC : (m:ℂ)^M ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hm)
  have principal : patternSum D z (0 : Fin M → Fin m) = (D.card : ℂ) := by
    simp [patternSum]
  have ex := pattern_expansion (m := m) D z roots
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ 0), principal] at ex
  have eq : (m:ℂ)^M * ((patternCount D z:ℂ) - (D.card:ℂ)/(m:ℂ)^M) =
      ∑ e ∈ I, patternSum D z e := by
    rw [mul_sub, show (m:ℂ)^M*((D.card:ℂ)/(m:ℂ)^M) = D.card by field_simp]
    dsimp [I]
    linear_combination -ex
  have hc : (I.card:ℝ) ≤ (m:ℝ)^M := by
    have h := Finset.card_le_univ I
    simpa using (show (I.card:ℝ) ≤ Fintype.card (Fin M → Fin m) by exact_mod_cast h)
  have bound : ‖∑ e ∈ I, patternSum D z e‖ ≤ (m:ℝ)^M*W := calc
    _ ≤ ∑ e ∈ I, ‖patternSum D z e‖ := norm_sum_le _ _
    _ ≤ ∑ _e ∈ I, W := Finset.sum_le_sum (fun e he => nonprincipal e (Finset.mem_erase.mp he).1)
    _ ≤ (m:ℝ)^M*W := by simpa [nsmul_eq_mul] using mul_le_mul_of_nonneg_right hc hW
  rw [← eq, norm_mul, norm_pow, Complex.norm_nat] at bound
  have pos : 0 < (m:ℝ)^M := pow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)) _
  have res := le_of_mul_le_mul_left bound pos
  have liftR : ((patternCount D z:ℂ) - (D.card:ℂ)/(m:ℂ)^M) =
      (((patternCount D z:ℝ) - (D.card:ℝ)/(m:ℝ)^M : ℝ) : ℂ) := by push_cast; rfl
  simpa only [liftR, Complex.norm_real, Real.norm_eq_abs] using res

/-- Removing exceptional inputs from a complete sum costs at most their number
when each summand has absolute value at most one. -/
private theorem restrict_sum [Fintype K] (D : Finset K) (f : K → ℂ)
    (size : ∀ x, ‖f x‖ ≤ 1) {W : ℝ} (full : ‖∑ x, f x‖ ≤ W) :
    ‖∑ x ∈ D, f x‖ ≤ W + (Fintype.card K - D.card : ℕ) := by
  classical
  have eq := Finset.sum_sdiff (Finset.subset_univ D) (f := f)
  have exc : ‖∑ x ∈ Finset.univ \ D, f x‖ ≤ (Fintype.card K - D.card : ℕ) := calc
    _ ≤ ∑ x ∈ Finset.univ \ D, ‖f x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ Finset.univ \ D, (1:ℝ) := Finset.sum_le_sum (fun x _ => size x)
    _ = _ := by simp [Finset.card_sdiff (Finset.subset_univ D)]
  rw [show ∑ x ∈ D, f x = (∑ x, f x) - ∑ x ∈ Finset.univ \ D, f x by rw [← eq]; abel]
  exact (norm_sub_le _ _).trans (add_le_add full exc)

/-- The number of regular parameters where every character condition holds. -/
noncomputable def prescribedCount {F : Type*} [Field F] (χ : MulChar F ℂ)
    (P : Fin M → K → F) (target : Fin M → ℂ) (D : Finset K) : ℕ :=
  open Classical in (D.filter (fun x => ∀ i, χ (P i x) = target i)).card

/-- Counts prescribed values of an actual character. The only input on sums is a
uniform bound for the classical, complete, unweighted sums of the products of
the original functions. Removing their zeros has an additive cost independent of
the number of exponent vectors. -/
theorem character_count_bound {F : Type*} [Field F] [Fintype K] [NeZero m]
    (χ : MulChar F ℂ) (order : χ^m = 1) (P : Fin M → K → F) (target : Fin M → ℂ)
    (ht : ∀ i, target i^m = 1) (D : Finset K) (regular : ∀ x ∈ D, ∀ i, P i x ≠ 0)
    {W : ℝ} (hW : 0 ≤ W)
    (weil : ∀ e : Fin M → Fin m, e ≠ 0 → ‖∑ x : K, χ (∏ i, (P i x)^(e i:ℕ))‖ ≤ W) :
    |(prescribedCount χ P target D:ℝ) - (D.card:ℝ)/(m:ℝ)^M| ≤ W + (Fintype.card K - D.card : ℕ) := by
  classical
  let z (i : Fin M) (x : K) := χ (P i x) / target i
  have hm := NeZero.ne m
  have tne (i : Fin M) : target i ≠ 0 := fun h => by simpa [h, zero_pow hm] using ht i
  have root (u : F) (hu : u ≠ 0) : χ u ^ m = 1 := by
    rw [← χ.pow_apply' hm, order, MulChar.one_apply (isUnit_iff_ne_zero.2 hu)]
  have vals (u : F) : ‖χ u‖ ≤ 1 := by
    by_cases hu : u = 0
    · simp [hu,χ.map_zero]
    · exact (Complex.norm_eq_one_of_pow_eq_one (root u hu) hm).le
  have roots (x : K) (hx : x ∈ D) (i : Fin M) : z i x ^ m = 1 := by
    simp only [z, div_pow, root _ (regular x hx i), ht, div_one]
  have countEq : patternCount D z = (D.filter (fun x => ∀ i, χ (P i x) = target i)).card := by
    unfold patternCount
    congr 1
    ext x
    simp [z, div_eq_one_iff_eq (tne _)]
  unfold prescribedCount
  rw [← countEq]
  apply pattern_discrepancy D z roots (by positivity)
  intro e he
  let v := ∏ i, target i^(e i:ℕ)
  have vNorm : ‖v‖ = 1 := by
    simp only [v, norm_prod, norm_pow, fun i => Complex.norm_eq_one_of_pow_eq_one (ht i) hm,
      one_pow, Finset.prod_const_one]
  have factor : patternSum D z e = (∑ x ∈ D, χ (∏ i, (P i x)^(e i:ℕ))) / v := by
    rw [patternSum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro x _
    simp only [z, v, div_pow, Finset.prod_div_distrib, map_prod, map_pow]
  rw [factor, norm_div, vNorm, div_one]
  exact restrict_sum D _ (fun x => vals _) (weil e he)

/-- Full-field normalization: every removed input costs at most two in the final
error, even when M grows. In particular any main term larger than the right-hand
side implies that the prescribed character pattern occurs. -/
theorem character_count_full_main {F : Type*} [Field F] [Fintype K] [NeZero m]
    (χ : MulChar F ℂ) (order : χ^m = 1) (P : Fin M → K → F) (target : Fin M → ℂ)
    (ht : ∀ i, target i^m = 1) (D : Finset K) (regular : ∀ x ∈ D, ∀ i, P i x ≠ 0)
    {W : ℝ} (hW : 0 ≤ W)
    (weil : ∀ e : Fin M → Fin m, e ≠ 0 → ‖∑ x : K, χ (∏ i, (P i x)^(e i:ℕ))‖ ≤ W) :
    |(prescribedCount χ P target D:ℝ) - Fintype.card K/(m:ℝ)^M| ≤
      W + 2*(Fintype.card K - D.card : ℕ) := by
  have h := character_count_bound χ order P target ht D regular hW weil
  have hs : (D.card:ℝ) ≤ Fintype.card K := by exact_mod_cast Finset.card_le_univ D
  have cap : (1:ℝ) ≤ (m:ℝ)^M := one_le_pow_of_one_le
    (by exact_mod_cast (Nat.one_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne m)))) _
  have shift : |(D.card:ℝ)/(m:ℝ)^M - Fintype.card K/(m:ℝ)^M| ≤
      (Fintype.card K - D.card : ℕ) := by
    rw [← sub_div, abs_div, abs_of_nonpos (sub_nonpos.mpr hs), abs_of_pos (by linarith : 0 < (m:ℝ)^M),
      neg_sub, Nat.cast_sub (Finset.card_le_univ D)]
    exact div_le_self (sub_nonneg.mpr hs) cap
  have triangle := abs_sub_le (prescribedCount χ P target D : ℝ)
    ((D.card:ℝ)/(m:ℝ)^M) (Fintype.card K/(m:ℝ)^M)
  linarith

/-- Strict dominance in the full-field estimate produces a regular witness. -/
theorem character_pattern_exists {F : Type*} [Field F] [Fintype K] [NeZero m]
    (χ : MulChar F ℂ) (order : χ^m = 1) (P : Fin M → K → F) (target : Fin M → ℂ)
    (ht : ∀ i, target i^m = 1) (D : Finset K) (regular : ∀ x ∈ D, ∀ i, P i x ≠ 0)
    {W : ℝ} (hW : 0 ≤ W)
    (weil : ∀ e : Fin M → Fin m, e ≠ 0 → ‖∑ x : K, χ (∏ i, (P i x)^(e i:ℕ))‖ ≤ W)
    (dominates : W + 2*(Fintype.card K - D.card : ℕ) < Fintype.card K/(m:ℝ)^M) :
    ∃ x ∈ D, ∀ i, χ (P i x) = target i := by
  classical
  have h := (abs_le.mp (character_count_full_main χ order P target ht D regular hW weil)).1
  have pos : 0 < (prescribedCount χ P target D : ℝ) := by linarith
  have hp : 0 < prescribedCount χ P target D := by exact_mod_cast pos
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hp
  exact ⟨x,(Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩

/-- Uniform logarithmic patterns, combining the complete-sum estimate, the
two parameter regimes and the explicit threshold. Q is the size of the actual
field of summation; L can be the logarithm of the extension field size. -/
theorem logarithmic_character_witness {F : Type*} [Field F] [Fintype K] [Nonempty K] [NeZero m]
    {l : ℕ} (hm : 2 ≤ m) (χ : MulChar F ℂ) (order : χ^m = 1)
    (P : Fin M → K → F) (target : Fin M → ℂ) (ht : ∀ i, target i^m = 1)
    (D : Finset K) (regular : ∀ x ∈ D, ∀ i, P i x ≠ 0)
    {W C L : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C)
    (weil : ∀ e : Fin M → Fin m, e ≠ 0 → ‖∑ x : K, χ (∏ i, (P i x)^(e i:ℕ))‖ ≤ W)
    (error : W + 2*(Fintype.card K - D.card : ℕ) ≤
      C*(1+Real.log (Fintype.card K))*Real.exp (3*Real.log (Fintype.card K)/4))
    (threshold : 256*(C+1) ≤ Real.log (Fintype.card K))
    (budget : (l:ℝ)*(32*(m:ℝ)^2*Real.log m) ≤ L)
    (regime : (M ≤ 2*m*l ∧ L = Real.log (Fintype.card K)) ∨
      (M ≤ m*l ∧ L ≤ 4*m*Real.log (Fintype.card K))) :
    ∃ x ∈ D, ∀ i, χ (P i x) = target i := by
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have h1 : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hb := pattern_budget hm budget regime (Real.log_nonneg h1)
  exact character_pattern_exists χ order P target ht D regular hW weil
    (error.trans_lt (main_term_dominates hq hm hC threshold hb))

end BlockingCurves.PhaseCharacter
