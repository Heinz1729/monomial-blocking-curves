import CubicCocycles
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.LinearCombination

/-! A first-cohomology bound from the two meridian families. A mixed tensor
word has both an x-active (true) and a y-active (false) standard position.
A single coboundary makes every active coordinate zero on all mixed words. -/
namespace BlockingCurves.CubicUnsigned
open CubicCocycles

variable {I J G : Type*} [Group G] [DecidableEq I]
abbrev BasisWord (J : Type*) := J → Bool
abbrev Space (J : Type*) := BasisWord J → ℂ

/-- The local row at a standard factor is negation on its active half.
A different finite factor acts only on its own tensor coordinate, so preserves
vanishing on slices of a spectator coordinate. -/
structure TensorRows (P : Meridians G (Option I)) (ρ : G →* Module.End ℂ (Space J))
    (idx : J ↪ I) : Prop where
  xrow : ∀ j f w, w j = true → ρ (P.x (some (idx j))) f w = -f w
  yrow : ∀ j f w, w j = false → ρ (P.y (some (idx j))) f w = -f w
  xlocal : ∀ (i : I) j, idx j ≠ i → ∀ f : Space J, (∀ w, w j = false → f w = 0) →
    ∀ w, w j = false → ρ (P.x (some i)) f w = 0
  ylocal : ∀ (i : I) j, idx j ≠ i → ∀ f : Space J, (∀ w, w j = true → f w = 0) →
    ∀ w, w j = true → ρ (P.y (some i)) f w = 0

variable (P : Meridians G (Option I)) {ρ : G →* Module.End ℂ (Space J)}
    {idx : J ↪ I} (R : TensorRows P ρ idx)
private abbrev X (i : I) := P.x (some i)
private abbrev Y (i : I) := P.y (some i)

private theorem edge (R : TensorRows P ρ idx) (f : crossed ρ) (w : BasisWord J) {j k : J}
    (hj : w j = true) (hk : w k = false) :
    f.val (X P (idx j)) w = f.val (Y P (idx k)) w := by
  have h : some (idx j) ≠ some (idx k) := by
    intro he
    have t := idx.injective (Option.some.inj he)
    subst k; simp [hj] at hk
  have h' := congrFun (commutation f (P.commute _ _ h)) w
  simp only [Pi.sub_apply] at h'
  rw [R.xrow j _ w hj, R.yrow k _ w hk] at h'
  change f.val (P.x _) w = f.val (P.y _) w
  linear_combination h' / 2

/-- Choose one standard position. For each basis word use its active meridian
value divided by two as the coordinate of the coboundary to subtract. -/
private noncomputable def pivot (s : J) : crossed ρ →ₗ[ℂ] Space J where
  toFun f w := (if w s then f.val (X P (idx s)) w else f.val (Y P (idx s)) w) / 2
  map_add' f g := by funext w; cases h : w s <;> simp [h,add_div]
  map_smul' a f := by funext w; cases h : w s <;> simp [h,mul_div_assoc]

private noncomputable def normalized (s : J) : crossed ρ →ₗ[ℂ] crossed ρ :=
  LinearMap.id - (boundary ρ).comp (pivot P (idx := idx) s)

private theorem pivot_zero (R : TensorRows P ρ idx) (f : crossed ρ) (s : J) (w : BasisWord J) :
    (if w s then ((normalized P (idx := idx) s) f).val (X P (idx s)) w
     else ((normalized P (idx := idx) s) f).val (Y P (idx s)) w) = 0 := by
  cases h : w s <;> simp only [h, Bool.false_eq_true, if_false, if_true]
  · change f.val _ w - ((pivot P s f) w - ρ (Y P (idx s)) (pivot P s f) w) = 0
    rw [R.yrow _ _ _ h]; simp [pivot,h]
  · change f.val _ w - ((pivot P s f) w - ρ (X P (idx s)) (pivot P s f) w) = 0
    rw [R.xrow _ _ _ h]; simp [pivot,h]

private theorem active_zero (R : TensorRows P ρ idx) (f : crossed ρ) (s : J)
    (pivot0 : ∀ w : BasisWord J,
      (if w s then f.val (X P (idx s)) w else f.val (Y P (idx s)) w) = 0)
    (xt : ∀ i, f.val (X P i) (fun _ => true) = 0)
    (yf : ∀ i, f.val (Y P i) (fun _ => false) = 0) (w : BasisWord J) :
    (∀ j, w j = true → f.val (X P (idx j)) w = 0) ∧
    (∀ j, w j = false → f.val (Y P (idx j)) w = 0) := by
  cases h : w s with
  | true =>
    have h0 : f.val (X P (idx s)) w = 0 := by simpa [h] using pivot0 w
    have hy (j) (hj : w j = false) := (edge P R f w h hj).symm.trans h0
    refine ⟨?_, hy⟩
    intro j hj
    by_cases e : ∃ k, w k = false
    · obtain ⟨k,hk⟩ := e; exact (edge P R f w hj hk).trans (hy k hk)
    · have eq : w = fun _ => true := by funext i; cases hi : w i <;> simp_all
      rw [eq]; exact xt _
  | false =>
    have h0 : f.val (Y P (idx s)) w = 0 := by simpa [h] using pivot0 w
    have hx (j) (hj : w j = true) := (edge P R f w hj h).trans h0
    refine ⟨hx,?_⟩
    intro j hj
    by_cases e : ∃ k, w k = true
    · obtain ⟨k,hk⟩ := e; exact (edge P R f w hk hj).symm.trans (hx k hk)
    · have eq : w = fun _ => false := by funext i; cases hi : w i <;> simp_all
      rw [eq]; exact yf _

private def xSample (idx : J ↪ I) (i : I) : BasisWord J := fun j => decide (idx j ≠ i)
private def ySample (idx : J ↪ I) (i : I) : BasisWord J := fun j => decide (idx j = i)

/-- All finite meridian values vanish if the active coordinates vanish and the
one remaining sample per finite meridian vanishes. -/
private theorem finite_zero (R : TensorRows P ρ idx) (f : crossed ρ)
    (activeX : ∀ j w, w j = true → f.val (X P (idx j)) w = 0)
    (activeY : ∀ j w, w j = false → f.val (Y P (idx j)) w = 0)
    (xs : ∀ i, f.val (X P i) (xSample idx i) = 0)
    (ys : ∀ i, f.val (Y P i) (ySample idx i) = 0) :
    (∀ i, f.val (X P i) = 0) ∧ (∀ i, f.val (Y P i) = 0) := by
  constructor
  · intro i; funext w
    change f.val (X P i) w = 0
    by_cases bad : ∃ j, idx j ≠ i ∧ w j = false
    · obtain ⟨j,ne,hj⟩ := bad
      have h := congrFun (commutation f (P.commute (some i) (some (idx j)) (by simpa using ne.symm))) w
      simp only [Pi.sub_apply] at h
      rw [R.yrow j _ w hj, activeY j w hj, R.xlocal i j ne _ (activeY j) w hj] at h
      linear_combination h / 2
    · by_cases e : ∃ j, idx j = i ∧ w j = true
      · obtain ⟨j,rfl,hj⟩ := e; exact activeX j w hj
      · have hw : w = xSample idx i := by
          funext j
          by_cases h : idx j = i <;> cases hj : w j <;> simp_all [xSample]
        rw [hw]; exact xs i
  · intro i; funext w
    change f.val (Y P i) w = 0
    by_cases bad : ∃ j, idx j ≠ i ∧ w j = true
    · obtain ⟨j,ne,hj⟩ := bad
      have h := congrFun (commutation f (P.commute (some (idx j)) (some i) (by simpa using ne))) w
      simp only [Pi.sub_apply] at h
      rw [R.xrow j _ w hj, activeX j w hj, R.ylocal i j ne _ (activeX j) w hj] at h
      linear_combination -h / 2
    · by_cases e : ∃ j, idx j = i ∧ w j = false
      · obtain ⟨j,rfl,hj⟩ := e; exact activeY j w hj
      · have hw : w = ySample idx i := by
          funext j
          by_cases h : idx j = i <;> cases hj : w j <;> simp_all [ySample]
        rw [hw]; exact ys i

/-- Only one coordinate of each infinity meridian remains after the finite
meridians vanish, by commutation with every opposite finite generator. -/
private theorem all_zero (R : TensorRows P ρ idx) (f : crossed ρ)
    (xf : ∀ i, f.val (X P i) = 0) (yf : ∀ i, f.val (Y P i) = 0)
    (xInf : f.val (P.x none) (fun _ => true) = 0)
    (yInf : f.val (P.y none) (fun _ => false) = 0) : f = 0 := by
  apply vanish_on_generators P f
  · rintro (_|i)
    · funext w; change f.val (P.x none) w = 0
      by_cases bad : ∃ j, w j = false
      · obtain ⟨j,hj⟩ := bad
        have h := commutation f (P.commute none (some (idx j)) (by simp))
        rw [show f.val (P.y (some (idx j))) = 0 from yf _, map_zero] at h
        have hh := congrFun h w
        simp only [Pi.sub_apply, Pi.zero_apply] at hh
        rw [R.yrow j _ w hj] at hh
        linear_combination hh / 2
      · have he : w = fun _ => true := by funext j; cases hj : w j <;> simp_all
        rw [he]; exact xInf
    · exact xf i
  · rintro (_|i)
    · funext w; change f.val (P.y none) w = 0
      by_cases bad : ∃ j, w j = true
      · obtain ⟨j,hj⟩ := bad
        have h := commutation f (P.commute (some (idx j)) none (by simp))
        rw [show f.val (P.x (some (idx j))) = 0 from xf _, map_zero] at h
        have hh := congrFun h w
        simp only [Pi.sub_apply, Pi.zero_apply] at hh
        rw [R.xrow j _ w hj] at hh
        linear_combination -hh / 2
      · have he : w = fun _ => false := by funext j; cases hj : w j <;> simp_all
        rw [he]; exact yInf
    · exact yf i

/-- For each side: one constant-word sample per finite label, one more
sample per finite label, and a single sample for the label at infinity. -/
private abbrev Samples (I : Type*) := Bool × (I ⊕ Option I)
private def atSample (idx : J ↪ I) : Samples I → G × BasisWord J
  | (true, Sum.inl i) => (X P i, fun _ => true)
  | (false, Sum.inl i) => (Y P i, fun _ => false)
  | (true, Sum.inr (some i)) => (X P i, xSample idx i)
  | (false, Sum.inr (some i)) => (Y P i, ySample idx i)
  | (true, Sum.inr none) => (P.x none, fun _ => true)
  | (false, Sum.inr none) => (P.y none, fun _ => false)

private def observe (idx : J ↪ I) : crossed ρ →ₗ[ℂ] (Samples I → ℂ) where
  toFun f t := f.val (atSample P idx t).1 (atSample P idx t).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- At most 4ℓ+2 independent H¹-coordinates. The argument is independent of
the number of standard factors, provided one such factor supplies the pivot. -/
theorem finrank_le [Fintype I] (R : TensorRows P ρ idx) (s : J) :
    FiniteDimensional.finrank ℂ (HOne ρ) ≤ 4 * Fintype.card I + 2 := by
  classical
  let Q := (LinearMap.range (boundary ρ)).mkQ
  obtain ⟨L,hL⟩ := Q.exists_rightInverse_of_surjective (Submodule.range_mkQ _)
  let N := normalized P (idx := idx) (ρ := ρ) s
  let obs := (observe P idx).comp (N.comp L)
  have inj : Function.Injective obs := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    let f := N (L c)
    have z (t : Samples I) : f.val (atSample P idx t).1 (atSample P idx t).2 = 0 :=
      congrFun hc t
    have act := active_zero P R f s (pivot_zero P R (L c) s)
      (fun i => z (true,Sum.inl i)) (fun i => z (false,Sum.inl i))
    have fin := finite_zero P R f (fun j w => (act w).1 j) (fun j w => (act w).2 j)
      (fun i => z (true,Sum.inr (some i))) (fun i => z (false,Sum.inr (some i)))
    have hf := all_zero P R f fin.1 fin.2 (z (true,Sum.inr none)) (z (false,Sum.inr none))
    have hc' : Q (L c) = c := DFunLike.congr_fun hL c
    have hq : Q f = Q (L c) := by
      change Q (L c - boundary ρ (pivot P (idx := idx) s (L c))) = _
      rw [map_sub, show Q (boundary ρ (pivot P (idx := idx) s (L c))) = 0 from
        (Submodule.Quotient.mk_eq_zero _).mpr ⟨_,rfl⟩, sub_zero]
    rw [← hc', ← hq, hf, map_zero]
  have h := LinearMap.finrank_le_finrank_of_injective inj
  have dim : FiniteDimensional.finrank ℂ (HOne ρ) ≤
      2 * (Fintype.card I + (Fintype.card I + 1)) := by
    simpa [Samples,FiniteDimensional.finrank_fintype_fun_eq_card, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_option] using h
  omega

end BlockingCurves.CubicUnsigned
