import StatementComparison
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

/-! Horizontal cosets and projection lifts for powers of a finite-field norm. -/

namespace BlockingCurves.NormPencil

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- An additive translate cover of the power values in the ground field. -/
def PowerCover (m : ℕ) (T : Finset F) : Prop := ∀ b : F, ∃ u : F, u ^ m - b ∈ T

private theorem cover_exists (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    ∃ k : ℕ, ∃ T : Finset F, T.card = k ∧ PowerCover m T :=
  ⟨_, Finset.univ, rfl, fun _ => ⟨0, Finset.mem_univ _⟩⟩

noncomputable def coverNumber (F : Type*) [Field F] [Fintype F] (m : ℕ) : ℕ :=
  open Classical in Nat.find (cover_exists F m)

theorem coverNumber_attained (F : Type*) [Field F] [Fintype F] (m : ℕ) :
    ∃ T : Finset F, T.card = coverNumber F m ∧ PowerCover m T := by
  classical
  exact Nat.find_spec (cover_exists F m)

theorem coverNumber_le {m : ℕ} {T : Finset F} (hT : PowerCover m T) :
    coverNumber F m ≤ T.card := by
  classical
  exact Nat.find_min' (cover_exists F m) ⟨T, rfl, hT⟩

theorem coverNumber_one (F : Type*) [Field F] [Fintype F] : coverNumber F 1 = 1 := by
  classical
  apply le_antisymm
  · have h : PowerCover 1 ({0} : Finset F) := fun b => ⟨b, by simp⟩
    simpa using coverNumber_le h
  · obtain ⟨T, hcard, hT⟩ := coverNumber_attained F 1
    obtain ⟨u, hu⟩ := hT 0
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨_, hu⟩

theorem coverNumber_lt_card {m : ℕ} (hm : 0 < m) : coverNumber F m < Fintype.card F := by
  classical
  let T : Finset F := Finset.univ.erase 0
  have hc : PowerCover m T := by
    intro b
    by_cases hb : b = 0
    · exact ⟨1, by simp [T,hb]⟩
    · exact ⟨0, by simp [T,zero_pow hm.ne',hb]⟩
  have hT : T.card < (Finset.univ : Finset F).card :=
    Finset.card_lt_card (Finset.erase_ssubset (Finset.mem_univ (0:F)))
  exact (coverNumber_le hc).trans_lt (by simpa using hT)

theorem exists_projection (F E : Type*) [Field F] [Field E] [Algebra F E] :
    ∃ π : E →ₗ[F] F, ∀ c : F, π (algebraMap F E c) = c := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap F E).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)
  exact ⟨π, fun c => LinearMap.congr_fun hπ c⟩

variable (π : E →ₗ[F] F) (split : ∀ c : F, π (algebraMap F E c) = c)

def coordinates : E ≃ (LinearMap.ker π) × F where
  toFun x := (⟨x - algebraMap F E (π x), by simp [LinearMap.mem_ker, split]⟩, π x)
  invFun t := t.1.1 + algebraMap F E t.2
  left_inv x := sub_add_cancel x _
  right_inv := by
    rintro ⟨⟨z, hz⟩, c⟩
    change π z = 0 at hz
    ext <;> simp [hz, split]

noncomputable def slice (S : Finset E) (z : (LinearMap.ker π)) : Finset F :=
  open Classical in Finset.univ.filter (fun c : F => z.1 + algebraMap F E c ∈ S)

theorem slice_mem (S : Finset E) (z : (LinearMap.ker π)) (c : F) :
    c ∈ slice π S z ↔ z.1 + algebraMap F E c ∈ S := by
  classical
  simp [slice]

theorem card_slices (S : Finset E) :
    S.card = ∑ z : (LinearMap.ker π), (slice π S z).card := by
  classical
  let e := coordinates π split
  let eS : (S : Type _) ≃ (Σ z : (LinearMap.ker π), ↥(slice π S z)) :=
    { toFun := fun x => ⟨(e x).1, (e x).2, (slice_mem π S _ _).2 (by
                            change e.symm (e x) ∈ S
                            simp)⟩
      invFun := fun t => ⟨e.symm (t.1, t.2.1), (slice_mem π S _ _).1 t.2.2⟩
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
      right_inv := by
        rintro ⟨z, c, hc⟩
        dsimp only
        have h := e.apply_symm_apply (z, c)
        refine Sigma.ext (congrArg Prod.fst h) ((Subtype.heq_iff_coe_eq ?_).2 (congrArg Prod.snd h))
        intro u
        exact iff_of_eq (congrArg (fun v => u ∈ slice π S v) (congrArg Prod.fst h)) }
  simpa only [Fintype.card_coe, Fintype.card_sigma] using Fintype.card_congr eS

/-- The contribution of all horizontal lines, one optimal cover in each additive coset. -/
theorem horizontal_lower {m d : ℕ} (himage : ∀ x : E, ∃ u : F, x ^ d = algebraMap F E (u ^ m))
    (S : Finset E) (hS : ∀ b : E, ∃ x : E, x ^ d - b ∈ S) :
    Fintype.card (LinearMap.ker π) * coverNumber F m ≤ S.card := by
  classical
  rw [card_slices π split S]
  calc
    _ = ∑ _ : (LinearMap.ker π), coverNumber F m := by simp
    _ ≤ _ := Finset.sum_le_sum (fun z _ => coverNumber_le (T := slice π S z) (by
      intro b
      obtain ⟨x, hx⟩ := hS (algebraMap F E b - z.1)
      obtain ⟨u, hu⟩ := himage x
      refine ⟨u, (slice_mem π S z _).2 ?_⟩
      rw [hu] at hx
      rwa [map_sub, show z.1 + (algebraMap F E (u ^ m) - algebraMap F E b) =
        algebraMap F E (u ^ m) - (algebraMap F E b - z.1) by ring]))

noncomputable def lift (π : E →ₗ[F] F) (T : Finset F) : Finset E :=
  open Classical in Finset.univ.filter (fun x : E => π x ∈ T)

theorem mem_lift {T : Finset F} {x : E} : x ∈ lift π T ↔ π x ∈ T := by
  classical
  simp [lift]

theorem card_lift (T : Finset F) : (lift π T).card = Fintype.card (LinearMap.ker π) * T.card := by
  classical
  rw [card_slices π split]
  have hs (z : (LinearMap.ker π)) : slice π (lift π T) z = T := by
    ext c
    rw [slice_mem, mem_lift, map_add, split, show π z.1 = 0 from z.2, zero_add]
  simp [hs]

/-- For the projection lift, the genuine remaining condition is the value distribution of
the norm on the kernel of each linear functional x ↦ π(ax). -/
theorem graphHits_lift {m d : ℕ} (T : Finset F) (hT : PowerCover m T)
    (hkernel : ∀ (a : E) (u : F), ∃ x : E, π (a*x) = 0 ∧ x ^ d = algebraMap F E (u ^ m)) :
    GraphHits (fun x : E => x ^ d) (lift π T : Set E) := by
  intro a b
  obtain ⟨u, hu⟩ := hT (π b)
  obtain ⟨x, hx, hx'⟩ := hkernel a u
  exact ⟨x, (mem_lift π).2 (by simpa only [map_sub, hx', split, hx, sub_zero] using hu)⟩

end BlockingCurves.NormPencil
