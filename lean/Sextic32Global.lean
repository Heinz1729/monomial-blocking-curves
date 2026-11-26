import Sextic32Geometry
import Sextic32Search
import StatementComparison

namespace Sextic32
open BlockingCurves

set_option maxRecDepth 10000 in
private theorem rootSix (u : Bits) : (u ^ 26) ^ 6 = u := by
  have h : ∀ x : E, ((Bits.mk x) ^ 26) ^ 6 = Bits.mk x := by decide
  exact h u.val

theorem affine_image {S : Set Bits} (hs : GraphHits (fun x : Bits => x^6) S)
    {a : Bits} (ha : a ≠ 0) (c : Bits) :
    GraphHits (fun x : Bits => x^6) ((fun s => a^6*s+c) '' S) := by
  intro m b
  obtain ⟨x,hx⟩ := hs (m/a^5) ((b+c)/a^6)
  refine ⟨a*x, _, hx, ?_⟩
  field_simp [ha]
  ring

theorem normalize_with_image (S : Finset Bits) (hs : GraphHits (fun x : Bits => x^6) (S : Set Bits))
    {a b : Bits} (ha : a ∈ S) (hb : b ∈ S) (hab : b ≠ a) :
    ∃ u c : Bits, u ≠ 0 ∧ ∃ V : Finset Bits, V = S.image (fun x => u*x+c) ∧
      V.card = S.card ∧ 0 ∈ V ∧ 1 ∈ V ∧
      GraphHits (fun x : Bits => x^6) (V : Set Bits) := by
  let u := (b-a)⁻¹
  have hu : u ≠ 0 := inv_ne_zero (sub_ne_zero.mpr hab)
  let f := fun x => u*x-u*a
  have hf : Function.Injective f := fun x y he => (mul_right_inj' hu).mp (sub_left_inj.mp he)
  refine ⟨u, -(u*a), hu, S.image f, by simp [f, sub_eq_add_neg],
    Finset.card_image_of_injective _ hf, Finset.mem_image.mpr ⟨a, ha, sub_self _⟩,
    Finset.mem_image.mpr ⟨b, hb, ?_⟩, ?_⟩
  · change u*b-u*a = 1
    rw [← mul_sub]
    exact inv_mul_cancel (sub_ne_zero.mpr hab)
  · have h := affine_image hs (pow_ne_zero 26 hu) (-(u*a))
    rw [rootSix] at h
    simpa only [Finset.coe_image, f, sub_eq_add_neg] using h

theorem encode_normalized (V : Finset Bits) (h0 : 0 ∈ V) (h1 : 1 ∈ V) :
    ∃ ys : List E, ys.Sublist pool ∧ ys.length = V.card - 2 ∧ params (0 :: 1 :: ys) = V := by
  let ys := pool.filter fun x => decide (Bits.mk x ∈ V)
  have he (x : E) : x ∈ elems := (show ∀ e : E, e ∈ elems by decide) x
  have hm (x : Bits) : x ∈ params ys ↔ x ≠ 0 ∧ x ≠ 1 ∧ x ∈ V := by
    cases x with
    | mk z =>
      have hz : (Bits.mk z ≠ 0) ↔ z ≠ 0 := not_congr (bitsEquiv.injective.eq_iff.symm)
      have ho : (Bits.mk z ≠ 1) ↔ z ≠ 1 := not_congr (bitsEquiv.injective.eq_iff.symm)
      simp only [mem_params, ys, pool, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
        decide_eq_true_eq, Bits.val, he, true_and, hz, ho, and_assoc]
  have hset : params ys = (V.erase 0).erase 1 := by
    ext x
    simp only [hm, Finset.mem_erase]
    exact and_left_comm
  have hp : pool.Nodup := by decide
  have hn : ys.Nodup := hp.filter _
  have hlen : ys.length = V.card - 2 := by
    have hcard' := List.toFinset_card_of_nodup (hn.map (f := Bits.mk) (fun _ _ h => Bits.mk.inj h))
    change (params ys).card = _ at hcard'
    rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨one_ne_zero,h1⟩),
      Finset.card_erase_of_mem h0, List.length_map] at hcard'
    omega
  have hsum : params (0::1::ys) = V := by
    ext x
    have hz : x.val = 0 ↔ x = 0 := bitsEquiv.injective.eq_iff (a := x) (b := 0)
    have ho : x.val = 1 ↔ x = 1 := bitsEquiv.injective.eq_iff (a := x) (b := 1)
    rw [mem_params, List.mem_cons, List.mem_cons, ← mem_params x ys, hm, hz, ho]
    constructor
    · rintro (rfl | rfl | ⟨_,_,hx⟩) <;> assumption
    · intro hx
      by_cases e : x = 0
      · exact Or.inl e
      by_cases e' : x = 1
      · exact Or.inr (Or.inl e')
      exact Or.inr (Or.inr ⟨e,e',hx⟩)
  exact ⟨ys, List.filter_sublist _, hlen, hsum⟩

private theorem six_impossible (cert : allMiss pool 4 [] = true)
    (S : Finset Bits) (hcard : S.card = 6) (hs : GraphHits (fun x : Bits => x^6) (S : Set Bits)) :
    False := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  obtain ⟨_,_,_,V,_,hV,h0,h1,hh⟩ := normalize_with_image S hs ha hb hab.symm
  obtain ⟨ys, hsub, hl, hsum⟩ := encode_normalized V h0 h1
  have hlen : ys.length = 4 := by omega
  have hb := (hits_iff_projective ys).2
    (hsum ▸ (projectiveBlocks_iff_graphHits (by decide : 2 ≤ 6) _).2 hh)
  have hmiss := allMiss_sound hsub
    [] ((congrArg (fun n => allMiss pool n []) hlen).trans cert)
  simp only [List.nil_append] at hmiss
  exact Bool.noConfusion (hb.symm.trans hmiss)

private theorem field_minimum (cert : allMiss pool 4 [] = true) :
    IsLeast {r : ℕ | ∃ S : Finset Bits, S.card = r ∧ ProjectiveBlocks 6 (S : Set Bits)} 7 := by
  constructor
  · exact ⟨params (0 :: 1 :: witness), by decide, (hits_iff_projective _).1 witness_verified⟩
  · rintro r ⟨S,rfl,hS⟩
    by_contra! hsmall
    have h32 : (Finset.univ : Finset Bits).card = 32 := by
      rw [Finset.card_univ, Fintype.card_congr bitsEquiv]
      decide
    obtain ⟨V,hSV,_,hc⟩ := Finset.exists_intermediate_set (6-S.card)
      (show 6-S.card+S.card ≤ (Finset.univ : Finset Bits).card by omega) (Finset.subset_univ S)
    apply six_impossible cert V (by omega)
    intro m b
    obtain ⟨x,hx⟩ := ((projectiveBlocks_iff_graphHits (by decide) _).1 hS) m b
    exact ⟨x, hSV hx⟩

noncomputable def fieldEquiv : Bits ≃+* GaloisField 2 5 :=
  FiniteField.ringEquivOfCardEq (by
    rw [GaloisField.card 2 5 (by decide), Fintype.card_congr bitsEquiv]
    decide)

theorem projective_sextic_minimum :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField 2 5), S.card = r ∧
      ProjectiveBlocks 6 (S : Set (GaloisField 2 5))} 7 :=
  projective_minimum_ringEquiv fieldEquiv (by decide) (field_minimum no_normalized_six)

/-- The same minimum in the projective-plane statement of Question 5.4. -/
theorem pencil_minimum : AsgarliGhiocaYip.isPencilMinimum (GaloisField 2 5) 6 7 :=
  (AGY_minimum_iff (by decide) 7).2 projective_sextic_minimum

end Sextic32
