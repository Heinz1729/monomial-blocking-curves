import CubicGlobal

namespace BlockingCurves.Cubic41

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Fifth roots of unity, in the ordinary residue coordinates of the field. -/
def H : Finset F := {1, 10, 16, 18, 37}

theorem mem_H_iff (x : F) : x ∈ H ↔ x^5 = 1 := by
  revert x
  decide

/-- The affine action on translation parameters. -/
def affine (a b : F) (S : Finset F) : Finset F := S.image (fun s => a*s+b)

theorem affine_comp (a b c d : F) (S : Finset F) :
    affine a b (affine c d S) = affine (a*c) (a*d+b) S := by
  simp only [affine, Finset.image_image, Function.comp_apply]
  apply Finset.image_congr
  intro x _
  change a*(c*x+d)+b = (a*c)*x+(a*d+b)
  ring

def orbit : Finset (Finset F) :=
  (((Finset.univ : Finset F).erase 0).product (Finset.univ : Finset F)).image
    (fun ab => affine ab.1 ab.2 H)

theorem mem_orbit_iff (S : Finset F) :
    S ∈ orbit ↔ ∃ a b : F, a ≠ 0 ∧ affine a b H = S := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩,hp,he⟩ := Finset.mem_image.mp h
    exact ⟨a,b,(Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1,he⟩
  · rintro ⟨a,b,ha,rfl⟩
    exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩,Finset.mem_univ _⟩,rfl⟩

theorem normalized_representatives :
    affine 2 9 H = {0,1,4,11,29} ∧ affine 5 33 H = {0,1,13,31,38} ∧
    affine 3 12 H = {0,1,15,19,25} ∧ affine 11 30 H = {0,1,17,23,27} := by decide

theorem stabilizer_exact : ∀ a b : F, a ≠ 0 →
    (affine a b H = H ↔ b = 0 ∧ a ∈ H) := by decide



theorem affine_hit_iff (a b : F) (ha : a ≠ 0) (S : Finset F) :
    GraphHits (fun x : F => x^3) (affine a b S : Set F) ↔
    GraphHits (fun x : F => x^3) (S : Set F) := by
  have hcube : ∀ s : F, (s^27)^3 = s := by decide
  have h := cubic_affine_image_iff (S : Set F) (pow_ne_zero 27 ha) b
  rw [hcube] at h
  simpa only [affine, Finset.coe_image] using h


#print axioms stabilizer_exact

/-- The units whose underlying residues lie in H form the fifth-root subgroup. -/
def fifthRootSubgroup : Subgroup Fˣ where
  carrier := {z | (z : F) ^ 5 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    change (u : F)^5 = 1 at hu
    change (v : F)^5 = 1 at hv
    change ((u : F) * (v : F))^5 = 1
    rw [mul_pow,hu,hv,one_mul]
  inv_mem' := by
    intro u hu
    change (u : F)^5 = 1 at hu
    change ((u⁻¹ : Fˣ) : F)^5 = 1
    rw [Units.val_inv_eq_inv_val]
    rw [inv_pow, hu, inv_one]

theorem unit_mem_iff (z : Fˣ) : z ∈ fifthRootSubgroup ↔ (z : F) ∈ H :=
  (mem_H_iff z).symm

private theorem orbit_closed (S : Finset F) {a : F} (ha : a ≠ 0) (b : F)
    (hS : S ∈ orbit) : affine a b S ∈ orbit := by
  obtain ⟨c,d,hc,rfl⟩ := (mem_orbit_iff S).mp hS
  exact (mem_orbit_iff _).mpr ⟨a*c,a*d+b,mul_ne_zero ha hc,(affine_comp ..).symm⟩

private theorem recover (S : Finset F) {a : F} (ha : a ≠ 0) (b : F)
    (hs : affine a b S ∈ orbit) : S ∈ orbit := by
  have rev := orbit_closed (affine a b S) (inv_ne_zero ha) (-(a⁻¹*b)) hs
  rw [affine_comp] at rev
  simpa [ha,affine] using rev

theorem H_blocks : GraphHits (fun x : F => x^3) (H : Set F) := by
  apply (affine_hit_iff 2 9 (by decide) H).mp
  rw [normalized_representatives.1]
  exact five_blocks

/-- All projective blocking pencils of minimum size form the single affine orbit of H. -/
theorem projective_cubic_orbit (S : Finset F) :
    S.card = 5 ∧ ProjectiveBlocks 3 (S : Set F) ↔ S ∈ orbit := by
  rw [projectiveBlocks_iff_graphHits (by decide : 2 ≤ 3)]
  constructor
  · rintro ⟨hcard,hs⟩
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    obtain ⟨u,c,hu,V,hV,hn,h0,h1,hv⟩ := normalize_with_image S hs ha hb hab.symm
    apply recover S hu c
    change S.image (fun s => u*s+c) ∈ orbit
    rw [← hV]
    have h := normalized_five V (hn.trans hcard) h0 h1 hv
    obtain ⟨hA,hB,hC,hD⟩ := normalized_representatives
    apply (mem_orbit_iff V).mpr
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨2,9,by decide,hA⟩
    · exact ⟨5,33,by decide,hB⟩
    · exact ⟨3,12,by decide,hC⟩
    · exact ⟨11,30,by decide,hD⟩
  · intro hs
    obtain ⟨a,b,ha,rfl⟩ := (mem_orbit_iff _).mp hs
    refine ⟨?_,(affine_hit_iff a b ha H).mpr H_blocks⟩
    have hinj : Function.Injective (fun x : F => a*x+b) := by
      intro x y hxy
      exact (mul_right_inj' ha).mp (add_right_cancel hxy)
    rw [affine, Finset.card_image_of_injective _ hinj]
    decide

#print axioms projective_cubic_orbit

/-- Two affine maps give the same pencil precisely when their relative map stabilizes H. -/
private theorem fiber_equation (a b c d : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    affine a b H = affine c d H ↔ ∃ h ∈ H, a = c*h ∧ b = d := by
  constructor
  · intro he
    have h := congrArg (affine c⁻¹ (-(c⁻¹*d))) he
    simp only [affine_comp] at h
    rw [inv_mul_cancel hc, add_right_neg] at h
    have hid : affine 1 0 H = H := by simp [affine]
    rw [hid] at h
    obtain ⟨hb, hh⟩ := (stabilizer_exact _ _ (mul_ne_zero (inv_ne_zero hc) ha)).mp h
    refine ⟨c⁻¹*a,hh,?_,?_⟩
    · rw [← mul_assoc, mul_inv_cancel hc, one_mul]
    · apply (mul_right_inj' (inv_ne_zero hc)).mp
      exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hb)
  · rintro ⟨h,hh,haeq,hbeq⟩
    rw [haeq,hbeq]
    have hh0 : h ≠ 0 := fun hz => by subst h; exact (by decide : (0:F) ∉ H) hh
    have hs := (stabilizer_exact h 0 hh0).mpr ⟨rfl,hh⟩
    have he := affine_comp c d h 0 H
    simpa [hs] using he.symm

private theorem divide_count (t : ℕ) (ht : 1640 = t*5) : t=328 := by omega


private def parameters : Finset (F × F) :=
  ((Finset.univ : Finset F).erase 0).product Finset.univ
private def imageH (t : F × F) : Finset F := affine t.1 t.2 H

private theorem count_parameters : parameters.card = 1640 := by
  change (((Finset.univ : Finset F).erase 0) ×ˢ (Finset.univ : Finset F)).card = 1640
  rw [Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]

private theorem cfiber (s : Finset F) (hs : s ∈ orbit) : (parameters.filter (fun t => imageH t = s)).card = 5 := by
    obtain ⟨c,d,hc,rfl⟩ := (mem_orbit_iff s).mp hs
    let i : F → F × F := fun h => (c*h,d)
    have hi : Function.Injective i := by
      intro x y he
      exact (mul_right_inj' hc).mp (congrArg Prod.fst he)
    have he : parameters.filter (fun t => imageH t = affine c d H) = H.image i := by
      ext ⟨a,b⟩
      constructor
      · intro h
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp h
        have ha := (Finset.mem_erase.mp (Finset.mem_product.mp hp).1).1
        obtain ⟨t,ht,rfl,rfl⟩ := (fiber_equation a b c d ha hc).mp he
        exact Finset.mem_image.mpr ⟨t,ht,rfl⟩
      · intro h
        obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h
        have hat : c*t = a := congrArg Prod.fst he
        have hbd : d = b := congrArg Prod.snd he
        subst a
        subst b
        have ht0 : t ≠ 0 := fun eq => by subst t; exact (by decide : (0:F) ∉ H) ht
        have ha := mul_ne_zero hc ht0
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨ha,Finset.mem_univ _⟩,Finset.mem_univ _⟩,
          (fiber_equation _ _ _ _ ha hc).mpr ⟨t,ht,rfl,rfl⟩⟩
    rw [he, Finset.card_image_of_injective _ hi]
    decide

private theorem count_uniform {α β : Type*} [DecidableEq β] (A : Finset α)
    (f : α → β) (O : Finset β) (hO : A.image f = O) (hA : A.card = 1640)
    (h : ∀ s ∈ O, (A.filter (fun t => f t = s)).card = 5) : O.card = 328 := by
  have hcount := Finset.card_eq_sum_card_image f A
  rw [hO, Finset.sum_congr rfl h, Finset.sum_const, smul_eq_mul,hA] at hcount
  exact divide_count _ hcount

/-- There are precisely 328 distinct parameter sets in the affine orbit. -/
theorem orbit_card : orbit.card = 328 :=
  count_uniform parameters imageH orbit rfl count_parameters cfiber

#print axioms orbit_card
end BlockingCurves.Cubic41

