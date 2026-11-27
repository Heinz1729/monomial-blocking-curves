import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Index

/-! Exact affine sampling moments and the singular-direction bound. Sampling
all direction vectors, including zero, makes the two-point evaluation a
bijection. The multiplicative subgroup gives a lower bound for the mass of
the orbit of every nonzero direction. -/
namespace BlockingCurves.PhaseDirection

open Finset
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

noncomputable def mark (C : Finset E) (x : E) : ℝ :=
  open Classical in if x ∈ C then 1 else 0

def point (t : F) (p : E × E) : E := p.2 + p.1 * algebraMap F E t

noncomputable def hits (F : Type*) [Field F] [Fintype F] [Algebra F E] (C : Finset E)
    (v b : E) : ℝ := ∑ t : F, mark C (point t (v,b))

noncomputable def mean (F : Type*) [Fintype F] (C : Finset E) : ℝ :=
  Fintype.card F * (C.card / (Fintype.card E : ℝ))

private def pairMap (t u : F) (h : t ≠ u) : (E × E) ≃ (E × E) where
  toFun p := (point t p, point u p)
  invFun p := let v := (p.2-p.1)/(algebraMap F E u-algebraMap F E t)
              (v,p.1-v*algebraMap F E t)
  left_inv := by
    rintro ⟨v,b⟩
    have hn := sub_ne_zero.mpr ((algebraMap F E).injective.ne h.symm)
    ext <;> dsimp [point] <;> field_simp <;> ring
  right_inv := by
    rintro ⟨x,y⟩
    have hn := sub_ne_zero.mpr ((algebraMap F E).injective.ne h.symm)
    apply Prod.ext
    · dsimp [point]; abel
    · dsimp [point]; field_simp; ring

private theorem score_sum (C : Finset E) : (∑ x : E, mark C x) = C.card := by
  classical
  simp [mark]

private theorem centered_single (C : Finset E) (t u : F) :
    let ρ := (C.card:ℝ) / Fintype.card E
    (∑ p : E × E, (mark C (point t p)-ρ)*(mark C (point u p)-ρ)) =
      if t=u then (C.card:ℝ)*(Fintype.card E - C.card) else 0 := by
  classical
  let ρ := (C.card:ℝ) / Fintype.card E
  let w := fun x => mark C x - ρ
  have q0 : (Fintype.card E:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_pos.ne'
  have eq : (Fintype.card E:ℝ)*ρ = C.card := by dsimp [ρ]; field_simp
  have avg : ∑ x, w x = 0 := by simp [w, Finset.sum_sub_distrib,score_sum,nsmul_eq_mul,eq]
  have sq (x : E) : (mark C x)^2 = mark C x := by by_cases hx : x ∈ C <;> simp [mark,hx]
  change (∑ p : E × E, w (point t p)*w (point u p)) = _
  by_cases ht : t=u
  · subst u
    have diff : t ≠ t+1 := by simp
    have swap := (pairMap (E := E) t (t+1) diff).sum_comp (fun p : E × E => w p.1*w p.1)
    change (∑ p : E × E, w (point t p)*w (point t p)) = _ at swap
    rw [swap, if_pos rfl, Fintype.sum_prod_type]
    simp only [Finset.sum_const, card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    have ex (x : E) : w x * w x = mark C x - 2*ρ*mark C x + ρ^2 := by
      dsimp [w]
      linear_combination sq x
    simp_rw [ex]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, score_sum, Finset.sum_const,
      card_univ, nsmul_eq_mul]
    nlinarith only [congrArg (fun r : ℝ => r*(C.card:ℝ)) eq, congrArg (fun r : ℝ => r*r) eq]
  · have swap := (pairMap (E := E) t u ht).sum_comp (fun p : E × E => w p.1*w p.2)
    change (∑ p : E × E, w (point t p)*w (point u p)) = _ at swap
    rw [swap, if_neg ht, Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,avg,mul_zero]
    simp

/-- The exact centered second moment for a genuinely uniform affine map
from the ground field, including its constant maps. -/
theorem affine_variance (C : Finset E) :
    ∑ p : E × E, (hits F C p.1 p.2 - mean F C)^2 =
      (Fintype.card F:ℝ)*C.card*(Fintype.card E-C.card) := by
  classical
  let ρ := (C.card:ℝ) / Fintype.card E
  let w (t : F) (p : E × E) := mark C (point t p) - ρ
  have row (p : E × E) : (hits F C p.1 p.2 - mean F C)^2 = ∑ t : F, ∑ u : F, w t p * w u p := by
    rw [← Fintype.sum_mul_sum, ← sq, show (∑ t : F, w t p) = hits F C p.1 p.2 - mean F C by
      simp [w, hits, mean, ρ, Finset.sum_sub_distrib, nsmul_eq_mul]]
  simp_rw [row]
  rw [Finset.sum_comm]
  have fixed (t : F) : ∑ p : E × E, ∑ u : F, w t p * w u p =
      (C.card:ℝ)*(Fintype.card E-C.card) := by
    rw [Finset.sum_comm]
    simp only [w,ρ]
    simp_rw [centered_single C t]
    simp
  simp only [fixed, Finset.sum_const, card_univ, nsmul_eq_mul]
  ring

/-- For every direction the mean over base points is the same. -/
theorem direction_mean (C : Finset E) (v : E) :
    ∑ b : E, hits F C v b = (Fintype.card F:ℝ)*C.card := by
  classical
  unfold hits
  rw [Finset.sum_comm]
  have each (t : F) : ∑ b : E, mark C (point t (v,b)) = C.card := by
    change (∑ b : E, mark C (b+v*algebraMap F E t)) = _
    exact (Equiv.sum_comp (Equiv.addRight (v*algebraMap F E t)) (mark C)).trans (score_sum C)
  simp [each,nsmul_eq_mul]

/-- The subgroup considered as a set of field elements, excluding zero. -/
noncomputable def carrier (H : Subgroup Eˣ) : Finset E :=
  open Classical in (Finset.univ : Finset H).image (fun h : H => ((h:Eˣ):E))

theorem carrier_card (H : Subgroup Eˣ) :
    (carrier H).card = Fintype.card H := by
  classical
  rw [carrier, Finset.card_image_of_injective _ (fun _ _ he => Subtype.ext (Units.ext he)), card_univ]

private theorem scale_mem (H : Subgroup Eˣ) (g : H) (x : E) :
    ((g:Eˣ):E)*x ∈ carrier H ↔ x ∈ carrier H := by
  classical
  simp only [carrier, Finset.mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨g⁻¹*z,?_⟩
    change (((g:Eˣ)⁻¹ * (z:Eˣ) : Eˣ) : E) = x
    rw [Units.val_mul, hz, ← mul_assoc, Units.inv_mul, one_mul]
  · rintro ⟨z,rfl⟩
    exact ⟨g*z,rfl⟩

/-- Sum of squared deviations across all base points of a fixed nonzero direction.
The bound uses the multiplicative orbit inside the exact total variance. -/
theorem fixed_direction_variance (H : Subgroup Eˣ) (v : E) (hv : v ≠ 0) :
    ∑ b : E, (hits F (carrier H) v b - mean F (carrier H))^2 ≤
      (Fintype.card F:ℝ)*(Fintype.card E-(carrier H).card) := by
  classical
  let C := carrier H
  let R (u : E) := ∑ b : E, (hits F C u b - mean F C)^2
  let dir (g : H) := ((g:Eˣ):E)*v
  have hi : Function.Injective dir := fun _ _ he =>
    Subtype.ext (Units.ext (mul_right_cancel₀ hv he))
  have inv (g : H) (b : E) : hits F C (dir g) (((g:Eˣ):E)*b) = hits F C v b := by
    unfold hits
    apply Finset.sum_congr rfl
    intro t _
    rw [show point t (dir g,((g:Eˣ):E)*b) = ((g:Eˣ):E)*point t (v,b) by dsimp [point,dir]; ring]
    simp only [C,mark,scale_mem]
  have rr (g : H) : R (dir g) = R v := by
    have re := Equiv.sum_comp (Equiv.mulLeft₀ ((g:Eˣ):E) (g:Eˣ).ne_zero)
      (fun b => (hits F C (dir g) b - mean F C)^2)
    change (∑ b : E, (hits F C (dir g) (((g:Eˣ):E)*b) - mean F C)^2) = R (dir g) at re
    simpa only [inv] using re.symm
  have small : ∑ u ∈ Finset.univ.image dir, R u ≤ ∑ u : E, R u := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [Finset.sum_image (fun x _ y _ he => hi he)] at small
  simp only [rr, Finset.sum_const,card_univ,nsmul_eq_mul] at small
  have total := affine_variance (F := F) C
  rw [Fintype.sum_prod_type] at total
  change (∑ u, R u) = _ at total
  rw [total] at small
  letI : Nonempty H := ⟨1⟩
  have c : 0 < (Fintype.card H:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have cc : C.card = Fintype.card H := carrier_card H
  rw [cc] at small
  change R v ≤ _
  rw [← cc] at c
  apply le_of_mul_le_mul_left (a := (C.card:ℝ)) _ c
  simpa only [cc, mul_left_comm, mul_comm, mul_assoc] using small

theorem hits_eq_zero_iff (C : Finset E) (v b : E) :
    hits F C v b = 0 ↔ ∀ t : F, point t (v,b) ∉ C := by
  classical
  simp [hits,mark,Finset.filter_eq_empty_iff]

noncomputable def emptyCount {T : Type*} [Fintype T] (X : T → ℝ) : ℕ :=
  open Classical in (Finset.univ.filter (fun p => X p = 0)).card

private theorem empty_square {T : Type*} [Fintype T] (X : T → ℝ) (μ : ℝ) :
    (emptyCount X:ℝ)*μ^2 ≤ ∑ p : T, (X p-μ)^2 := by
  classical
  calc
    _ = ∑ p : T, (if X p = 0 then (1:ℝ) else 0) * μ^2 := by
      rw [← Finset.sum_mul]; simp [emptyCount]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro p _
      by_cases h : X p=0
      · simp [h]
      · simpa [h] using sq_nonneg (X p - μ)

/-- The empty-line fraction among all affine maps, useful for the nonsingular branch. -/
theorem affine_empty_fraction (C : Finset E) (hC : C.Nonempty) :
    (emptyCount (fun p : E × E => hits F C p.1 p.2):ℝ)/(Fintype.card E:ℝ)^2 ≤
      1 / mean F C := by
  have hs : (0:ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hq : (0:ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0:ℝ) < C.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
  have hμ : 0 < mean F C := mul_pos hs (div_pos hc hq)
  have eq : mean F C*(Fintype.card E:ℝ) = (Fintype.card F:ℝ)*C.card := by
    dsimp [mean]; field_simp
  have var := empty_square (fun p : E × E => hits F C p.1 p.2) (mean F C)
  rw [affine_variance] at var
  apply (div_le_div_iff (pow_pos hq 2) hμ).2
  apply le_of_mul_le_mul_right (a := mean F C) _ hμ
  nlinarith only [var, congrArg (fun u : ℝ => u * Fintype.card E) eq,
    mul_nonneg (mul_nonneg hs.le hc.le) hc.le]

/-- Every fixed nonzero direction has empty-fibre fraction at most
index/(s·density), with the true subgroup index and the actual set of misses. -/
theorem fixed_empty_fraction (H : Subgroup Eˣ) (v : E) (hv : v ≠ 0) :
    (emptyCount (hits F (carrier H) v):ℝ)/Fintype.card E ≤
      (H.index:ℝ) / mean F (carrier H) := by
  classical
  let C := carrier H
  have hs : (0:ℝ) < Fintype.card F := Nat.cast_pos.mpr Fintype.card_pos
  have hq : (0:ℝ) < Fintype.card E := Nat.cast_pos.mpr Fintype.card_pos
  letI : Nonempty H := ⟨1⟩
  have cardC : C.card = Fintype.card H := carrier_card H
  have hc : (1:ℝ) ≤ C.card := by rw [cardC]; exact_mod_cast Fintype.card_pos (α := H)
  have hμ : 0 < mean F C := mul_pos hs (div_pos (by linarith) hq)
  have eq : mean F C*(Fintype.card E:ℝ) = (Fintype.card F:ℝ)*C.card := by
    dsimp [mean]; field_simp
  have ord : H.index*C.card = Fintype.card E-1 := by rw [cardC,H.index_mul_card,Fintype.card_units]
  have ordR : (H.index:ℝ)*C.card = Fintype.card E-1 := by
    have ord' := congrArg (fun n : ℕ => (n:ℝ)) ord
    simpa [Nat.cast_sub (Nat.one_le_of_lt Fintype.card_pos)] using ord'
  have cap : (Fintype.card E:ℝ)-C.card ≤ H.index*C.card := by linarith
  have var := (empty_square (hits F C v) (mean F C)).trans (fixed_direction_variance H v hv)
  change (emptyCount (hits F C v):ℝ)/Fintype.card E ≤ (H.index:ℝ)/mean F C
  apply (div_le_div_iff hq hμ).2
  apply le_of_mul_le_mul_right (a := mean F C) _ hμ
  nlinarith only [var, mul_le_mul_of_nonneg_left cap hs.le,
    congrArg (fun u : ℝ => (H.index:ℝ)*u) eq]

end BlockingCurves.PhaseDirection
