import PencilCollisionCover

/-! Intersections of translated quadratic norm fibres and their value sets. -/
namespace BlockingCurves.NormQuadraticCollision

section Quadratic
variable {K : Type*} [Field K]

/-- The two conjugates are the only possible points with a prescribed
pair of norm values at distance one. -/
theorem norm_intersection (σ : K →+* K) {u v : K}
    (hu : u * σ u = v * σ v)
    (hv : (u - 1) * σ (u - 1) = (v - 1) * σ (v - 1)) :
    u = v ∨ u = σ v := by
  simp only [map_sub, map_one] at hv
  have hs : u + σ u = v + σ v := by linear_combination hu - hv
  have hp : (u - v) * (u - σ v) = 0 := by
    linear_combination u * hs - hu
  simpa only [mul_eq_zero, sub_eq_zero] using hp

/-- Any two distinct norm circles in the quadratic-pencil collision count
intersect in at most two points, in every characteristic. -/
theorem norm_fibre_card_le_two [Fintype K] [DecidableEq K] (σ : K →+* K)
    (w a b : K) (hw : w ≠ 0) :
    (Finset.univ.filter (fun x : K => x * σ x = a ∧
      (x-w) * σ (x-w) = b)).card ≤ 2 := by
  classical
  let S := Finset.univ.filter (fun x : K => x * σ x = a ∧ (x-w) * σ (x-w) = b)
  change S.card ≤ 2
  rcases S.eq_empty_or_nonempty with h | ⟨y, hy⟩
  · simp [h]
  have H {x : K} (hx : x ∈ S) : x = y ∨ x = w * σ (y / w) := by
    obtain ⟨hxa, hxb⟩ := (Finset.mem_filter.mp hx).2
    obtain ⟨hya, hyb⟩ := (Finset.mem_filter.mp hy).2
    have hN (z : K) : (z / w) * σ (z / w) = (z * σ z) / (w * σ w) := by
      rw [map_div₀]; ring
    have hone (z : K) : z / w - 1 = (z - w) / w := by field_simp
    rcases norm_intersection σ (u := x/w) (v := y/w) (by simp only [hN, hxa, hya])
        (by simp only [hone, hN, hxb, hyb]) with he | he
    · exact Or.inl ((div_left_inj' hw).mp he)
    · exact Or.inr (by calc
        x = w * (x / w) := by field_simp
        _ = _ := by rw [he])
  have hsub : S ⊆ {y, w * σ (y / w)} := by
    intro x hx
    simpa using H hx
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _ |>.trans (by simp))
end Quadratic


section CollisionCount
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
noncomputable local instance : DecidableEq E := Classical.decEq _

/-- The slope pencil of any function of the quadratic norm has at most
two ordered off-diagonal collisions per ordered pair of base norm values. -/
theorem collision_count (σ : E →+* E) (N : E → F)
    (hN : ∀ x, algebraMap F E (N x) = x * σ x) (φ : F → F) (a : E) (ha : a ≠ 0) :
    (PencilCollisionCover.offDiagonal (fun x => algebraMap F E (φ (N x)) - a*x)).card ≤
      2 * (Fintype.card F)^2 := by
  classical
  let g (x : E) := algebraMap F E (φ (N x)) - a*x
  let pair (p : E × E) := (N p.1, N p.2)
  change (PencilCollisionCover.offDiagonal g).card ≤ _
  apply (Finset.card_le_mul_card_image_of_maps_to (t := (Finset.univ : Finset (F × F)))
    (f := pair) (fun _ _ => Finset.mem_univ _) 2 ?_).trans_eq (by simp [sq])
  intro t _
  let W := (PencilCollisionCover.offDiagonal g).filter (fun p => pair p = t)
  let w := (algebraMap F E (φ t.1) - algebraMap F E (φ t.2))/a
  have info {p : E × E} (hp : p ∈ W) : N p.1 = t.1 ∧ N p.2 = t.2 ∧ p.1-p.2 = w ∧ p.1 ≠ p.2 := by
    obtain ⟨hc, ht⟩ := Finset.mem_filter.mp hp
    obtain ⟨hn, he⟩ := (Finset.mem_filter.mp hc).2
    have ht₁ : N p.1 = t.1 := congrArg Prod.fst ht
    have ht₂ : N p.2 = t.2 := congrArg Prod.snd ht
    refine ⟨ht₁, ht₂, (eq_div_iff ha).2 ?_, hn⟩
    dsimp [g] at he
    rw [ht₁, ht₂] at he
    linear_combination -he
  rcases W.eq_empty_or_nonempty with h | ⟨p, hp⟩
  · change W.card ≤ 2
    simp [h]
  have hw : w ≠ 0 := (info hp).2.2.1 ▸ sub_ne_zero.mpr (info hp).2.2.2
  apply le_trans _ (norm_fibre_card_le_two σ w (algebraMap F E t.1) (algebraMap F E t.2) hw)
  apply Finset.card_le_card_of_inj_on Prod.fst
  · intro v hv
    obtain ⟨h₁,h₂,h₃,_⟩ := info hv
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, (hN _).symm.trans (congrArg _ h₁), ?_⟩
    rw [show v.1-w = v.2 by linear_combination h₃, ← hN, h₂]
  · intro u hu v hv he
    apply Prod.ext he
    have hu' := (info hu).2.2.1
    have hv' := (info hv).2.2.1
    change u.1 = v.1 at he
    linear_combination he - hu' + hv'

theorem quadratic_value_density (σ : E →+* E) (N : E → F)
    (hN : ∀ x, algebraMap F E (N x) = x * σ x) (φ : F → F) (a : E) (ha : a ≠ 0)
    (hsize : Fintype.card E = (Fintype.card F)^2) :
    Fintype.card E ≤ 3 * (Finset.univ.image (fun x => algebraMap F E (φ (N x)) - a*x)).card := by
  classical
  let g (x : E) := algebraMap F E (φ (N x)) - a*x
  have ho : (PencilCollisionCover.offDiagonal g).card ≤ 2 * Fintype.card E := by
    rw [hsize]
    exact collision_count σ N hN φ a ha
  have hc := PencilCollisionCover.image_collision_bound g
  have hq := Fintype.card_pos (α := E)
  change Fintype.card E ≤ 3 * (Finset.univ.image g).card
  apply Nat.le_of_mul_le_mul_right (c := Fintype.card E) _ hq
  calc
      Fintype.card E * Fintype.card E = (Fintype.card E)^2 := (sq _).symm
      _ ≤ _ := hc
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.add_le_add_left ho _)
      _ = _ := by ring
end CollisionCount

end BlockingCurves.NormQuadraticCollision
