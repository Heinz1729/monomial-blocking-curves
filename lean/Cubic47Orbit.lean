import Cubic47Global

namespace BlockingCurves.Cubic47

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Dot's five translation parameters. -/
def seed : Finset F := {0, 1, 3, 15, 33}

def affine (a b : F) (S : Finset F) : Finset F := S.image (fun s => a*s+b)

private theorem affine_comp (a b c d : F) (S : Finset F) :
    affine a b (affine c d S) = affine (a*c) (a*d+b) S := by
  simp only [affine, Finset.image_image, Function.comp_apply]
  apply Finset.image_congr
  intro x _
  change a*(c*x+d)+b = (a*c)*x+(a*d+b)
  ring

private def parameters : Finset (F × F) :=
  ((Finset.univ : Finset F).erase 0).product Finset.univ

def orbit : Finset (Finset F) := parameters.image (fun t => affine t.1 t.2 seed)

theorem mem_orbit_iff (S : Finset F) :
    S ∈ orbit ↔ ∃ a b : F, a ≠ 0 ∧ affine a b seed = S := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hp,he⟩ := Finset.mem_image.mp h
    exact ⟨a,b,(Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1,he⟩
  · rintro ⟨a,b,ha,rfl⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩,Finset.mem_univ _⟩,rfl⟩

/-- Every enumerated representative is obtained by sending two seed elements to 0 and 1. -/
private theorem normalized_in_orbit (V : Finset F) (h : V ∈ normalizedSets) : V ∈ orbit := by
  let points : List F := [0,1,3,15,33]
  let isImage (S : Finset F) (p : F × F) :=
    decide (p.2 ≠ p.1 ∧ affine (p.2-p.1)⁻¹ (-((p.2-p.1)⁻¹*p.1)) seed = S)
  have cert : normalizedSets.all (fun S => (points.product points).any (isImage S)) = true := by
    decide
  obtain ⟨⟨r,s⟩,_,hp⟩ := List.any_eq_true.mp (List.all_eq_true.mp cert V h)
  obtain ⟨hs,he⟩ := of_decide_eq_true hp
  exact (mem_orbit_iff V).mpr ⟨_,_,inv_ne_zero (sub_ne_zero.mpr hs),he⟩

private theorem affine_hit_iff (a b : F) (ha : a ≠ 0) (S : Finset F) :
    GraphHits (fun x : F => x^3) (affine a b S : Set F) ↔
    GraphHits (fun x : F => x^3) (S : Set F) := by
  have hcube : ∀ s : F, (s^31)^3 = s := by decide
  have h := cubic_affine_image_iff (S : Set F) (pow_ne_zero 31 ha) b
  rw [hcube] at h
  simpa only [affine, Finset.coe_image] using h

/-- The minimum blocking pencils over F₄₇ are exactly the images of the seed. -/
theorem projective_cubic_orbit (S : Finset F) :
    S.card = 5 ∧ ProjectiveBlocks 3 (S : Set F) ↔ S ∈ orbit := by
  rw [projectiveBlocks_iff_graphHits (by decide : 2 ≤ 3)]
  constructor
  · rintro ⟨hcard,hs⟩
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    obtain ⟨u,c,hu,V,hV,hn,h0,h1,hv⟩ := normalize_with_image S hs ha hb hab.symm
    obtain ⟨k,t,hk,he⟩ := (mem_orbit_iff V).mp
      (normalized_in_orbit V (normalized_five V (hn.trans hcard) h0 h1 hv))
    have eq := congrArg (affine u⁻¹ (-(u⁻¹*c))) (he.trans hV)
    change affine u⁻¹ (-(u⁻¹*c)) (affine k t seed) =
      affine u⁻¹ (-(u⁻¹*c)) (affine u c S) at eq
    rw [affine_comp, affine_comp, inv_mul_cancel hu, add_right_neg] at eq
    exact (mem_orbit_iff S).mpr ⟨_,_,mul_ne_zero (inv_ne_zero hu) hk,by simpa [affine] using eq⟩
  · intro hs
    obtain ⟨a,b,ha,rfl⟩ := (mem_orbit_iff _).mp hs
    refine ⟨?_,(affine_hit_iff a b ha seed).mpr five_blocks⟩
    have inj : Function.Injective (fun x : F => a*x+b) := fun _ _ h =>
      (mul_right_inj' ha).mp (add_right_cancel h)
    rw [affine, Finset.card_image_of_injective _ inj]
    decide

theorem stabilizer_exact : ∀ a b : F, a ≠ 0 → affine a b seed = seed → a = 1 ∧ b = 0 := by
  decide

/-- Each of the 46 × 47 affine maps produces a different parameter set. -/
theorem orbit_card : orbit.card = 2162 := by
  have inj : Set.InjOn (fun t : F × F => affine t.1 t.2 seed) (parameters : Set (F × F)) := by
    rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
    have ha := (Finset.mem_erase.mp (Finset.mem_product.mp hab).1).1
    have hc := (Finset.mem_erase.mp (Finset.mem_product.mp hcd).1).1
    have h := congrArg (affine c⁻¹ (-(c⁻¹*d))) eq
    change affine c⁻¹ (-(c⁻¹*d)) (affine a b seed) =
      affine c⁻¹ (-(c⁻¹*d)) (affine c d seed) at h
    rw [affine_comp,affine_comp,inv_mul_cancel hc,add_right_neg] at h
    obtain ⟨h₁,h₂⟩ := stabilizer_exact _ _ (mul_ne_zero (inv_ne_zero hc) ha)
      (by simpa [affine] using h)
    have hac : a = c := (mul_right_inj' (inv_ne_zero hc)).mp (h₁.trans (inv_mul_cancel hc).symm)
    have hbd : b = d := (mul_right_inj' (inv_ne_zero hc)).mp
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h₂))
    exact Prod.ext hac hbd
  change (parameters.image _).card = _
  rw [Finset.card_image_iff.mpr inj]
  change (((Finset.univ : Finset F).erase 0) ×ˢ (Finset.univ : Finset F)).card = 2162
  rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

end BlockingCurves.Cubic47
