import PhaseDirectionSampling
import Projective

/-! Independent affine blocks complete the dividing-side projective cover. -/
namespace BlockingCurves.PhaseDividing
open Finset PhaseDirection
open scoped BigOperators

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
attribute [local instance] Classical.propDecidable

/-- The exact set of parameters meeting an affine line of slope a
and intercept b in the original translated monomial pencil. -/
noncomputable def valueSet (d:ℕ) (a b:E) : Finset E :=
  open Classical in univ.image (fun x:E => x^d-a*x-b)

private theorem block_budget {s q A p : ℝ} {n:ℕ} (hs:1<s) (hq:q=s^n)
    (hA:1≤A) (large:A^2≤s) (hp:0≤p) (rate:p≤A/s) :
    q^2*p^(4*n+1)<1 := by
  have hs0 : 0<s := by linarith
  have hps : p*s ≤ A := (le_div_iff hs0).1 rate
  have hsqr := sq_le_sq' (by nlinarith only [hps,hA,mul_nonneg hp hs0.le]) hps
  have smallSq : s*p^2 ≤ 1 := by
    apply le_of_mul_le_mul_right (a := s) _ hs0
    nlinarith only [hsqr,large]
  have small : p<1 := by
    by_contra! opposite
    have hp1 := mul_le_mul_of_nonneg_right opposite hp
    nlinarith only [smallSq,hs,mul_le_mul_of_nonneg_left hp1 hs0.le,
      mul_le_mul_of_nonneg_left opposite hs0.le]
  have hmany : q^2*p^(4*n) ≤ 1 := by
    have h := pow_le_one (2*n) (mul_nonneg hs0.le (sq_nonneg _)) smallSq
    calc q^2*p^(4*n) = (s*p^2)^(2*n) := by
           rw [hq,mul_pow,← pow_mul,← pow_mul]
           congr 1 <;> congr 1 <;> ring
         _ ≤ 1 := h
  calc q^2*p^(4*n+1) = (q^2*p^(4*n))*p := by rw [pow_succ p (4*n),mul_assoc]
       _ ≤ 1*p := mul_le_mul_of_nonneg_right hmany hp
       _ < 1 := by simpa using small

/-- Each draw is a uniform (direction, base point) in E². The union bound
covers every actual slope and intercept with at most (4n+1)s parameters. -/
theorem projective_block_sampling {n d:ℕ} (hd:2≤d)
    (size:Fintype.card E=Fintype.card F^n) {A:ℝ} (hA:1≤A) (large:A^2≤Fintype.card F)
    (hline:∀ a b:E, (emptyCount (fun p:E×E => hits F (valueSet d a b) p.1 p.2):ℝ)/
      (Fintype.card E:ℝ)^2 ≤ A/(Fintype.card F:ℝ)) :
    ∃ S:Finset E, ProjectiveBlocks d (S:Set E) ∧ S.card≤(4*n+1)*Fintype.card F := by
  classical
  let q := Fintype.card E
  let k := 4*n+1
  let miss (l:E×E) := (univ : Finset (E×E)).filter
    (fun p:E×E => hits F (valueSet d l.1 l.2) p.1 p.2=0)
  obtain ⟨lmax,_,hmax⟩ := exists_max_image (univ : Finset (E×E)) (fun l => (miss l).card) univ_nonempty
  let H := (miss lmax).card
  let bad (l:E×E) : Finset (Fin k → E×E) := Fintype.piFinset (fun _ => miss l)
  let U := (univ : Finset (E×E)).biUnion bad
  have hbad (l:E×E) : (bad l).card ≤ H^k := by
    simpa [bad] using pow_le_pow_left' (hmax l (mem_univ _)) k
  have hrate : (H:ℝ)/(q:ℝ)^2 ≤ A/(Fintype.card F:ℝ) := hline lmax.1 lmax.2
  have hq0 : 0<(q:ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hn := block_budget (show 1<(Fintype.card F:ℝ) by exact_mod_cast Fintype.one_lt_card)
    (show (q:ℝ)=(Fintype.card F:ℝ)^n by exact_mod_cast size) hA large
    (show 0≤(H:ℝ)/(q:ℝ)^2 by positivity) hrate
  have hstrict : q^2*H^k < (q^2)^k := by
    change (q:ℝ)^2*((H:ℝ)/(q:ℝ)^2)^k<1 at hn
    rw [div_pow,← mul_div_assoc,div_lt_iff (pow_pos (pow_pos hq0 2) k),one_mul] at hn
    exact_mod_cast hn
  have hsmall : U.card < Fintype.card (Fin k → E×E) := by
    have h := card_biUnion_le_card_mul (univ : Finset (E×E)) bad (H^k) (fun l _ => hbad l)
    simp only [card_univ,Fintype.card_prod,←sq] at h
    simpa [q,←sq] using h.trans_lt hstrict
  obtain ⟨f,hf⟩ : ∃ f:Fin k→E×E, f ∉ U := by
    by_contra! all
    rw [eq_univ_of_forall all,card_univ] at hsmall
    exact lt_irrefl _ hsmall
  let S := univ.image (fun it:Fin k × F => point it.2 (f it.1))
  refine ⟨S,(projectiveBlocks_iff_graphHits hd _).2 ?_,?_⟩
  · intro a b
    have hnot : f ∉ bad (a,b) := fun he => hf (mem_biUnion.mpr ⟨(a,b),mem_univ _,he⟩)
    change f ∉ Fintype.piFinset (fun _ : Fin k => miss (a,b)) at hnot
    rw [Fintype.mem_piFinset] at hnot
    push_neg at hnot
    obtain ⟨i,hi⟩ := hnot
    have hz : hits F (valueSet d a b) (f i).1 (f i).2 ≠ 0 := by simpa [miss] using hi
    have notEmpty := mt (hits_eq_zero_iff (F := F) (valueSet d a b) (f i).1 (f i).2).2 hz
    push_neg at notEmpty
    obtain ⟨t,ht⟩ := notEmpty
    obtain ⟨x,_,hx⟩ := mem_image.mp ht
    exact ⟨x, hx ▸ mem_image.mpr ⟨(i,t),mem_univ _,rfl⟩⟩
  · simpa [S,k] using card_image_le (s := (univ : Finset (Fin k × F)))
      (f := fun it:Fin k × F => point it.2 (f it.1))

end BlockingCurves.PhaseDividing
