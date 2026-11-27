import NormPencil
import NormFibreSampling
import NormSamplingSize

/-! Random shifts of an optimal horizontal cover in independent base-field cosets. -/
namespace BlockingCurves.NormPencil

open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
local instance : DecidableEq E := Classical.decEq _
variable (π : E →ₗ[F] F) (split : ∀ c : F, π (algebraMap F E c) = c)

/-- In each coset of the ground field, put a translate of the same finite set.
The distinguished element t₀ of the base set moves to the chosen transversal. -/
def shifted (T : Finset F) (t₀ : F) (u : LinearMap.ker π → F) : Finset E :=
  (Finset.univ : Finset (LinearMap.ker π)).biUnion (fun z =>
    T.image (fun v => z.1 + algebraMap F E (u z + v - t₀)))

theorem shifted_card (T : Finset F) (t₀ : F) (u : LinearMap.ker π → F) :
    (shifted π T t₀ u).card = Fintype.card (LinearMap.ker π) * T.card := by
  classical
  let e := coordinates π split
  let pack (p : LinearMap.ker π × F) : E := p.1.1 + algebraMap F E (u p.1 + p.2 - t₀)
  have hinj : Function.Injective pack := by
    rintro ⟨z,v⟩ ⟨z',v'⟩ he
    have h := e.symm.injective (a₁ := (z,u z+v-t₀)) (a₂ := (z',u z'+v'-t₀)) he
    have hz := congrArg Prod.fst h
    change z = z' at hz
    subst z'
    have hv := congrArg Prod.snd h
    simp only [Prod.mk.injEq, true_and]
    exact add_left_cancel (sub_left_inj.mp hv)
  have hs : shifted π T t₀ u = (Finset.univ ×ˢ T).image pack := by
    ext x
    simp [shifted, pack]
  rw [hs, Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_univ]

/-- Every horizontal line is still hit after arbitrary independent shifts. -/
theorem shifted_horizontal {m d : ℕ} (T : Finset F) (hT : PowerCover m T) (t₀ : F)
    (u : LinearMap.ker π → F)
    (hsur : ∀ v : F, ∃ x : E, x^d = algebraMap F E (v^m)) (b : E) :
    ∃ x : E, x^d-b ∈ shifted π T t₀ u := by
  classical
  let e := coordinates π split
  let z := (e (-b)).1
  let c := (e (-b)).2
  have hb : z.1 + algebraMap F E c = -b := e.symm_apply_apply (-b)
  obtain ⟨v,hv⟩ := hT (u z - t₀ - c)
  obtain ⟨x,hx⟩ := hsur v
  refine ⟨x, Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,Finset.mem_image.mpr
    ⟨_,hv,?_⟩⟩⟩
  rw [show u z + (v^m - (u z-t₀-c)) - t₀ = c+v^m by ring, map_add, ← add_assoc, hb, hx]
  ring

/-- Normalizing y=ax reduces the nonzero-slope tests to at most (s−1)q value sets. -/
def target (d : ℕ) (j : Fˣ × E) : Finset E :=
  Finset.univ.image (fun y : E => algebraMap F E (j.1 : F) * y^d - y - j.2)

theorem shifted_covers {m d : ℕ} (T : Finset F) (hT : PowerCover m T)
    (hsur : ∀ v : F, ∃ x : E, x^d = algebraMap F E (v^m))
    (hground : ∀ x : E, ∃ v : F, algebraMap F E v = x^d)
    (hbad : (∑ j : Fˣ × E, ∏ z : LinearMap.ker π,
        (Fintype.card F - (slice π (target d j) z).card)) <
      Fintype.card F ^ Fintype.card (LinearMap.ker π)) :
    ∃ S : Finset E, S.card = Fintype.card (LinearMap.ker π) * T.card ∧
      GraphHits (fun x : E => x^d) (S : Set E) := by
  classical
  obtain ⟨u, hu⟩ := NormFibreSampling.exists_transversal (fun j z => slice π (target d j) z) hbad
  obtain ⟨v,hv⟩ := hT 0
  let t₀ := v^m-0
  refine ⟨shifted π T t₀ u, shifted_card π split _ _ _, fun a b => ?_⟩
  by_cases ha : a = 0
  · simpa [ha] using shifted_horizontal π split T hT t₀ u hsur b
  obtain ⟨c,hc⟩ := hground a⁻¹
  have hc0 : c ≠ 0 := fun h => (pow_ne_zero _ (inv_ne_zero ha)) (hc.symm.trans (by simp [h]))
  let j : Fˣ × E := (Units.mk0 c hc0,b)
  obtain ⟨z,hz⟩ := hu j
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp ((slice_mem π _ _ _).1 hz)
  refine ⟨a⁻¹*y, Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, Finset.mem_image.mpr
    ⟨t₀,hv,?_⟩⟩⟩
  change algebraMap F E c * y^d - y - b = z.1 + algebraMap F E (u z) at hy
  dsimp only
  rw [add_sub_cancel_right, ← hy, hc, mul_pow, ← mul_assoc, mul_inv_cancel ha, one_mul]

/-- Every nonzero-slope value set contains at least one point of every base coset. -/
theorem target_row_nonempty {d : ℕ} (hground : ∀ x : E, ∃ v : F, algebraMap F E v = x^d)
    (j : Fˣ × E) (z : LinearMap.ker π) : (slice π (target d j) z).Nonempty := by
  classical
  let y := -z.1-j.2
  obtain ⟨v,hv⟩ := hground y
  refine ⟨(j.1 : F)*v, (slice_mem π _ _ _).2 (Finset.mem_image.mpr ⟨y,Finset.mem_univ _,?_⟩)⟩
  rw [map_mul, hv]
  dsimp [y]
  ring

theorem sparse_bad_count {d : ℕ}
    (hground : ∀ x : E, ∃ v : F, algebraMap F E v = x^d)
    (hnum : (Fintype.card F-1) * Fintype.card E *
        (Fintype.card F-1) ^ Fintype.card (LinearMap.ker π) <
      Fintype.card F ^ Fintype.card (LinearMap.ker π)) :
    (∑ j : Fˣ × E, ∏ z : LinearMap.ker π,
      (Fintype.card F - (slice π (target d j) z).card)) <
      Fintype.card F ^ Fintype.card (LinearMap.ker π) := by
  classical
  calc
    _ ≤ ∑ _ : Fˣ × E, ∏ _ : LinearMap.ker π, (Fintype.card F-1) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.prod_le_prod'
      intro z _
      exact Nat.sub_le_sub_left (Finset.card_pos.mpr (target_row_nonempty π hground j z)) _
    _ < _ := by simpa [Fintype.card_units, Nat.mul_assoc] using hnum

/-- When every target contains at least one third of the quadratic field,
AM–GM bounds the exact product of row misses by (2s/3)^s. -/
theorem dense_bad_count {d : ℕ} (s : ℕ) (hs : 25 ≤ s)
    (hF : Fintype.card F = s) (hE : Fintype.card E = s^2)
    (hcap : Fintype.card (LinearMap.ker π) = s)
    (hdens : ∀ j : Fˣ × E, Fintype.card E ≤ 3*(target d j).card) :
    (∑ j : Fˣ × E, ∏ z : LinearMap.ker π, (Fintype.card F - (slice π (target d j) z).card)) <
      Fintype.card F ^ Fintype.card (LinearMap.ker π) := by
  classical
  let c (j : Fˣ × E) (z : LinearMap.ker π) := Fintype.card F - (slice π (target d j) z).card
  have hs0 : (0:ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have H (j : Fˣ × E) : (∏ z, (c j z : ℝ)) ≤ ((2:ℝ)*s/3)^s := by
    have hsum : (∑ z, c j z) + (target d j).card = s^2 := by
      rw [card_slices π split (target d j), ← Finset.sum_add_distrib]
      have hrow (z : LinearMap.ker π) : c j z + (slice π (target d j) z).card = Fintype.card F :=
        Nat.sub_add_cancel (Finset.card_le_univ _)
      simp only [hrow, Finset.sum_const, Finset.card_univ, hcap, hF, nsmul_eq_mul, sq, Nat.cast_id]
    have hsum' : (∑ z, (c j z : ℝ)) + ((target d j).card : ℝ) = (s:ℝ)^2 := by exact_mod_cast hsum
    have hden := hdens j
    rw [hE] at hden
    have hden' : (s:ℝ)^2 ≤ 3*((target d j).card:ℝ) := by exact_mod_cast hden
    have hp := NormFibreSampling.prod_le_mean_pow (c j)
    rw [hcap] at hp
    apply hp.trans
    apply pow_le_pow_left (by positivity)
    apply (div_le_iff hs0).2
    nlinarith only [hsum', hden']
  have hn : (∑ j : Fˣ × E, ∏ z, (c j z : ℝ)) ≤
      ((s-1:ℕ):ℝ)*(s:ℝ)^2*((2:ℝ)*s/3)^s := by
    apply (Finset.sum_le_sum (fun j _ => H j)).trans_eq
    simp [Fintype.card_units, hE, hF, nsmul_eq_mul]
  have hth : ((s-1 : ℕ):ℝ)*(s:ℝ)^2*2^s < (3:ℝ)^s := by exact_mod_cast dense_threshold hs
  have hfin : (∑ j : Fˣ × E, ∏ z, (c j z : ℝ)) < (s:ℝ)^s := by
    apply hn.trans_lt
    rw [div_pow, mul_pow, ← mul_div_assoc]
    apply (div_lt_iff (by positivity : 0 < (3:ℝ)^s)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (mul_lt_mul_of_pos_right hth (pow_pos hs0 s))
  change (∑ j : Fˣ × E, ∏ z, c j z) < _
  rw [hcap, hF]
  exact_mod_cast hfin

end
end BlockingCurves.NormPencil
