import PiecewiseSyncUpper
import PiecewiseGroundEscape
import PiecewiseBoundedEscape
import PiecewiseLargeEscape

/-! The coefficient-period criterion at the minimum over actual graphs. -/
namespace BlockingCurves.PiecewiseFrobenius

open Finset PiecewiseWeil
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The algebraic labels used in the period are exactly the realized labels
of nonzero graph inputs. This includes composite indices. -/
theorem realize_power_label {m : ℕ} (hm : 0<m) (dvd : m ∣ Fintype.card E-1)
    (z:E) (root : z^m=1) : ∃ v : Eˣ, (v:E)^((Fintype.card E-1)/m)=z := by
  classical
  have nz : z≠0 := fun h => by simp [h,zero_pow hm.ne'] at root
  let u := Units.mk0 z nz
  have hu : u^m=1 := Units.ext (by simpa [u,Units.val_pow_eq_pow_val] using root)
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Eˣ)
  obtain ⟨j,hj⟩ := mem_powers_iff_mem_zpowers.2 (hg u)
  change g^j=u at hj
  let e := (Fintype.card E-1)/m
  have p : e*m=Fintype.card E-1 := Nat.div_mul_cancel dvd
  have ord : orderOf g ∣ j*m := orderOf_dvd_of_pow_eq_one (by rw [pow_mul,hj,hu])
  rw [orderOf_eq_card_of_forall_mem_zpowers hg,Fintype.card_units,←p] at ord
  obtain ⟨k,hk⟩ := Nat.dvd_of_mul_dvd_mul_right hm ord
  have he : (g^k)^e = u := by rw [←pow_mul,mul_comm k e,←hk,hj]
  exact ⟨g^k,by simpa only [Units.val_pow_eq_pow_val] using congrArg Units.val he⟩

theorem period_not_dvd_witnesses {m n : ℕ} (hm : 0<m)
    (dvd : m ∣ Fintype.card E-1) (table : E → Fˣ)
    (phase : ¬PiecewiseCandidates.coefficientPeriod (tableCoefficients m table) (table 1) ∣ n) :
    let e := (Fintype.card E-1)/m
    ∃ v w : Eˣ, (table ((v:E)^e):F)^n ≠ (table ((w:E)^e):F)^n := by
  classical
  intro e
  have noEq := mt (PiecewiseCandidates.coefficientPeriod_dvd_iff _ _ n).2 phase
  push_neg at noEq
  obtain ⟨c,hc,hne⟩ := noEq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp (show c ∈ (Polynomial.nthRootsFinset m E).image table from hc)
  obtain ⟨v,hv⟩ := realize_power_label hm dvd z ((Polynomial.mem_nthRootsFinset hm).1 hz)
  refine ⟨v,1,fun eq => hne (Units.ext ?_)⟩
  simpa only [Units.val_pow_eq_pow_val,hv,Units.val_one,one_pow] using eq

/- In an intermediate extension the character sum is on the base-field
slice. In relative degree one and in a large extension it is on E itself. -/
def tableWeilInput (F E : Type*) [Field F] [Fintype F] [Field E] [Fintype E]
    (m n : ℕ) : Prop :=
  if 2 ≤ n ∧ n < 4*m then ∀ χ : MulChar F ℂ, orderOf χ=m → PolynomialWeilBound m χ
  else ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ

/-- Both sides of the nonsynchronous estimate hold for an attained minimum.
The sole analytic premise is the one-variable Weil theorem on the field of
summation for the applicable range of n. -/
theorem nonsynchronous_table_minimum [FiniteDimensional F E] {m n : ℕ}
    (hm : 2 ≤ m) (hn : 0 < n) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E=Fintype.card F^n) (table : E → Fˣ)
    (phase : ¬PiecewiseCandidates.coefficientPeriod (tableCoefficients m table) (table 1) ∣ n)
    (threshold : 16384*(m:ℝ)^5 ≤ Real.log (Fintype.card E)) (weil : tableWeilInput F E m n) :
    let e := (Fintype.card E-1)/m
    let f := branchMap (fun x:E => (table (x^e):F))
    ∃ S : Finset E, GraphHits f (S:Set E) ∧
      (∀ T : Finset E, GraphHits f (T:Set E) → S.card ≤ T.card) ∧
      Real.log (Fintype.card E) < (S.card:ℝ)*(32*(m:ℝ)^2*Real.log m) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  classical
  intro e f
  have dvd : m ∣ Fintype.card E-1 := by
    rw [size,← NormPencil.normExponent_mul (Fintype.card F) n Fintype.card_pos,Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right divides _
  have dim : FiniteDimensional.finrank F E = n := Nat.pow_right_injective Fintype.one_lt_card
    ((card_eq_pow_finrank (K:=F) (V:=E)).symm.trans size)
  obtain ⟨v,w,sep⟩ := period_not_dvd_witnesses (by omega) dvd table phase
  obtain ⟨T,hT,hcard⟩ := cyclotomic_table_upper (by omega) dvd size (fun z:E => (table z:F)) v w sep
  let feasible := (univ : Finset (Finset E)).filter (fun V : Finset E => GraphHits f (V:Set E))
  have feasible_iff (V : Finset E) : V ∈ feasible ↔ GraphHits f (V:Set E) := by simp [feasible]
  obtain ⟨S,mem,least⟩ := exists_min_image feasible Finset.card ⟨T,(feasible_iff _).2 hT⟩
  have blocks := (feasible_iff _).1 mem
  refine ⟨S,blocks,fun V h => least _ ((feasible_iff _).2 h),?_,
    (Nat.cast_le.mpr (least _ ((feasible_iff _).2 hT))).trans hcard⟩
  by_contra! budget
  have two : table ((v:E)^e) ≠ table ((w:E)^e) := fun eq => sep (by rw [eq])
  by_cases mid : 2 ≤ n ∧ n < 4*m
  · have labels (u:Eˣ) : table ((u:E)^e) ∈ tableCoefficients m table := by
      apply mem_image.mpr
      refine ⟨_,(Polynomial.mem_nthRootsFinset (by omega : 0<m)).2 ?_,rfl⟩
      rw [←pow_mul,show e*m=Fintype.card E-1 from Nat.div_mul_cancel dvd]
      exact FiniteField.pow_card_sub_one_eq_one _ u.ne_zero
    exact PiecewiseBoundedEscape.bounded_table_escape hm (dim ▸ mid.1) (dim ▸ mid.2)
      divides table (tableCoefficients m table) labels ⟨v,w,two⟩ (tableCoefficients_card_le _ _) S
      (by simpa only [tableWeilInput,if_pos mid] using weil) threshold budget blocks
  · have law : ∀ χ : MulChar E ℂ, orderOf χ=m → PolynomialWeilBound m χ := by
      simpa only [tableWeilInput,if_neg mid] using weil
    by_cases ground : n=1
    · have sz : Fintype.card E=Fintype.card F := by simpa only [ground,pow_one] using size
      exact (not_lt_of_ge budget) (PiecewiseGroundEscape.ground_table_card_lower hm dvd sz
        (fun z:E => (table z:F)) S threshold law blocks)
    · have large : 4*m ≤ n := by omega
      exact PiecewiseLargeEscape.large_table_escape hm large divides size (fun z:E => (table z:F))
        (fun x => (table _).ne_zero) ⟨v,w,fun eq => two (Units.ext eq)⟩ S threshold budget law blocks

end BlockingCurves.PiecewiseFrobenius
