import Mathlib.LinearAlgebra.Dual
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Abel

/-! Crossed homomorphisms for the two sets of meridians in §14. The hypotheses
on generators and their actions are stated separately from the geometric
identification of the configuration group. Coefficients may be any
characteristic-zero field, in particular the 2-adic field. -/

namespace BlockingCurves.CubicCocycles

variable {K G V I : Type*} [Field K] [CharZero K] [Group G] [AddCommGroup V] [Module K V]
variable (ρ : G →* Module.End K V)

/-- Inhomogeneous group 1-cocycles, with the left-action convention. -/
def crossed : Submodule K (G → V) where
  carrier := {f | ∀ g h, f (g*h) = f g + ρ g (f h)}
  zero_mem' := by intro g h; simp
  add_mem' := by intro f h hf hh g k; change f (g*k) + h (g*k) = _; rw [hf, hh]; simp; abel
  smul_mem' := by intro c f hf g k; change c • f (g*k) = _; rw [hf]; simp [smul_add]

/-- The coboundary with value (1−ρ(g))z on g. -/
def boundary : V →ₗ[K] crossed ρ where
  toFun z := ⟨fun g => z - ρ g z, by
    intro g h
    simp only [map_mul, LinearMap.mul_apply, map_sub]
    abel⟩
  map_add' a b := by ext g; change a+b - ρ g (a+b) = _; simp; abel
  map_smul' c z := by ext g; change c • z - ρ g (c • z) = _; simp [smul_sub]

/-- First group cohomology as the usual explicit cocycle quotient. -/
abbrev HOne := (crossed ρ) ⧸ LinearMap.range (boundary ρ)

variable {ρ}

private theorem cocycle_mul (f : crossed ρ) (g h : G) :
    f.1 (g*h) = f.1 g + ρ g (f.1 h) := f.2 g h

private theorem cocycle_one (f : crossed ρ) : f.1 1 = 0 := by
  have eqn := cocycle_mul f 1 1
  simpa using eqn

private theorem commutation (f : crossed ρ) {g h : G} (c : Commute g h) :
    f.1 g - ρ h (f.1 g) = f.1 h - ρ g (f.1 h) := by
  have e : f.1 g + ρ g (f.1 h) = f.1 h + ρ h (f.1 g) := by
    rw [← cocycle_mul, c.eq, cocycle_mul]
  exact sub_eq_sub_iff_add_eq_add.mpr e

/-- The two meridian families generate; meridians in opposite families
with different labels commute. The label set may include infinity. -/
structure Meridians (G I : Type*) [Group G] where
  x : I → G
  y : I → G
  generate : Subgroup.closure (Set.range x ∪ Set.range y) = ⊤
  commute : ∀ i j, i ≠ j → Commute (x i) (y j)

variable (P : Meridians G I)

/-- A sign position acts by negation on both meridians. -/
def SignAt (ρ : G →* Module.End K V) (s : I) :=
  (∀ v, ρ (P.x s) v = -v) ∧ (∀ v, ρ (P.y s) v = -v)

private theorem vanish_on_generators (f : crossed ρ)
    (hx : ∀ i, f.1 (P.x i) = 0) (hy : ∀ i, f.1 (P.y i) = 0) : f = 0 := by
  apply Subtype.ext
  funext g
  change f.1 g = 0
  have hg : g ∈ Subgroup.closure (Set.range P.x ∪ Set.range P.y) := by
    rw [P.generate]; exact Subgroup.mem_top _
  refine Subgroup.closure_induction hg ?_ (cocycle_one f) ?_ ?_
  · rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
    exact hx i
    exact hy i
  · intro a b ha hb
    rw [cocycle_mul, ha, hb, map_zero, add_zero]
  · intro a ha
    have h := cocycle_mul f a⁻¹ a
    simpa [ha, cocycle_one] using h.symm

private theorem cancel_double (v : V) (h : v + v = 0) : v = 0 := by
  exact (smul_eq_zero.mp (show (2 : K) • v = 0 by rwa [two_smul])).resolve_left (by norm_num)

private theorem sign_equations {s : I} (hs : SignAt P ρ s) (f : crossed ρ)
    (hn : f.1 (P.x s) = 0) {i : I} (hi : i ≠ s) :
    f.1 (P.y i) = 0 ∧
    f.1 (P.x i) + f.1 (P.x i) = f.1 (P.y s) - ρ (P.x i) (f.1 (P.y s)) := by
  constructor
  · have e := commutation f (P.commute s i hi.symm)
    rw [hn, map_zero, sub_zero, hs.1, sub_neg_eq_add] at e
    exact cancel_double (K := K) _ e.symm
  · have e := commutation f (P.commute i s hi)
    rwa [hs.2, sub_neg_eq_add] at e

/-- Subtract the unique coboundary that kills the first meridian at s. -/
def normalize (s : I) (f : crossed ρ) : crossed ρ :=
  f - boundary ρ ((2 : K)⁻¹ • f.1 (P.x s))

private theorem half_double (v : V) : (2 : K)⁻¹ • v + (2 : K)⁻¹ • v = v := by
  rw [← two_smul K, smul_smul, mul_inv_cancel (by norm_num : (2:K) ≠ 0), one_smul]

theorem normalize_at_sign {s : I} (hs : SignAt P ρ s) (f : crossed ρ) :
    (normalize P s f).1 (P.x s) = 0 ∧
    (normalize P s f).1 (P.y s) = f.1 (P.y s) - f.1 (P.x s) := by
  constructor
  · change _ - (_ - ρ (P.x s) _) = 0
    rw [hs.1, sub_neg_eq_add, half_double, sub_self]
  · change _ - (_ - ρ (P.y s) _) = _
    rw [hs.2, sub_neg_eq_add, half_double]

/-- Difference of the two meridian values. At a sign position it is invariant
under coboundaries. -/
def jump (s : I) : crossed ρ →ₗ[K] V where
  toFun f := f.1 (P.y s) - f.1 (P.x s)
  map_add' f g := by change (f.1 _ + g.1 _) - (f.1 _ + g.1 _) = _; abel
  map_smul' c f := by change c • f.1 _ - c • f.1 _ = c • (_ - _); rw [smul_sub]

private theorem normalized_ext_zero {s : I} (hs : SignAt P ρ s) (f : crossed ρ)
    (hx : f.1 (P.x s) = 0) (hy : f.1 (P.y s) = 0) : f = 0 := by
  apply vanish_on_generators P
  · intro i
    by_cases hi : i = s
    · simpa [hi] using hx
    · have e := (sign_equations P hs f hx hi).2
      exact cancel_double (K := K) _ (by simpa [hy] using e)
  · intro i
    by_cases hi : i = s
    · simpa [hi] using hy
    · exact (sign_equations P hs f hx hi).1

theorem ker_jump_eq_boundaries {s : I} (hs : SignAt P ρ s) :
    LinearMap.ker (jump P (ρ := ρ) s) = LinearMap.range (boundary ρ) := by
  ext f
  change (f.1 (P.y s) - f.1 (P.x s) = 0) ↔ _
  constructor
  · intro h
    have he := normalize_at_sign P hs f
    have hz := normalized_ext_zero P hs _ he.1 (he.2.trans h)
    exact ⟨_, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨z, rfl⟩
    change (z - ρ (P.y s) z) - (z - ρ (P.x s) z) = 0
    rw [hs.1, hs.2, sub_self]

/-- The cohomology class embeds linearly by the single normalized value D(y_s). -/
def signMap {s : I} (hs : SignAt P ρ s) : HOne ρ →ₗ[K] V :=
  (LinearMap.range (boundary ρ)).liftQ (jump P s) (ker_jump_eq_boundaries P hs).ge

theorem signMap_injective {s : I} (hs : SignAt P ρ s) :
    Function.Injective (signMap P hs) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (ker_jump_eq_boundaries P hs).le)

private theorem mixed_difference {s i j : I} (hs : SignAt P ρ s)
    (hi : i ≠ s) (hj : j ≠ s) (hij : i ≠ j) (c : HOne ρ) :
    ρ (P.y j) (signMap P hs c - ρ (P.x i) (signMap P hs c)) =
      signMap P hs c - ρ (P.x i) (signMap P hs c) := by
  obtain ⟨f, rfl⟩ := (LinearMap.range (boundary ρ)).mkQ_surjective c
  let d := normalize P s f
  have hn := normalize_at_sign P hs f
  have hy := (sign_equations P hs d hn.1 hj).1
  have hu := (sign_equations P hs d hn.1 hi).2
  have hc := commutation d (P.commute i j hij)
  rw [hy, map_zero, sub_zero] at hc
  have fixed := (sub_eq_zero.mp hc).symm
  change ρ (P.y j) (jump P s f - ρ (P.x i) (jump P s f)) =
    jump P s f - ρ (P.x i) (jump P s f)
  have hn' : d.1 (P.y s) = jump P s f := hn.2
  rw [← hn', ← hu, map_add, fixed]

private theorem double_injective : Function.Injective (fun v : V => v+v) := by
  intro v w h
  change v+v = w+w at h
  apply sub_eq_zero.mp
  apply cancel_double (K := K)
  have e : v-w+(v-w) = (v+v)-(w+w) := by abel
  rw [e, h, sub_self]

/-- A second sign index forces both actions at every remaining index to fix the
normalized value. A standard factor has no such common invariant. -/
theorem fixed_of_two_signs {s t i : I} (hs : SignAt P ρ s) (ht : SignAt P ρ t)
    (hst : s ≠ t) (his : i ≠ s) (hit : i ≠ t) (c : HOne ρ) :
    ρ (P.x i) (signMap P hs c) = signMap P hs c ∧
    ρ (P.y i) (signMap P hs c) = signMap P hs c := by
  let h := signMap P hs c
  have a := mixed_difference P hs his hst.symm hit c
  have b := mixed_difference P hs hst.symm his hit.symm c
  change ρ (P.y t) (h - ρ (P.x i) h) = h - ρ (P.x i) h at a
  change ρ (P.y i) (h - ρ (P.x t) h) = h - ρ (P.x t) h at b
  rw [ht.2] at a
  rw [ht.1, sub_neg_eq_add, map_add] at b
  constructor
  · apply Eq.symm
    apply sub_eq_zero.mp
    apply cancel_double (K := K)
    exact neg_eq_iff_add_eq_zero.mp a
  · exact double_injective (K := K) b

theorem subsingleton_of_two_signs {s t i : I} (hs : SignAt P ρ s)
    (ht : SignAt P ρ t) (hst : s ≠ t) (his : i ≠ s) (hit : i ≠ t)
    (fixed : ∀ v, ρ (P.x i) v = v → ρ (P.y i) v = v → v = 0) :
    Subsingleton (HOne ρ) := by
  have hz (c : HOne ρ) : c = 0 := by
    apply signMap_injective P hs
    rw [map_zero]
    exact fixed _ (fixed_of_two_signs P hs ht hst his hit c).1
      (fixed_of_two_signs P hs ht hst his hit c).2
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem subsingleton_of_three_signs {s t i : I} (hs : SignAt P ρ s)
    (ht : SignAt P ρ t) (hi : SignAt P ρ i) (hst : s ≠ t)
    (his : i ≠ s) (hit : i ≠ t) : Subsingleton (HOne ρ) := by
  apply subsingleton_of_two_signs P hs ht hst his hit
  intro v hv _
  rw [hi.1] at hv
  exact cancel_double (K := K) _ (neg_eq_iff_add_eq_zero.mp hv)

section WordCoordinates

variable {J : Type*}
local notation "Words" => (J → Bool)
local notation "Coeffs" => (Words → K)

/-- Two endpoint coordinates of an array indexed by standard-factor basis words. -/
private def endpoints : Coeffs →ₗ[K] K × K where
  toFun f := (f (fun _ => false), f (fun _ => true))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- In the basis e,f of the two fixed lines of the standard representation,
the f-coordinate of the x-reflection, and the e-coordinate of the y-reflection,
are both negated. These are the only two matrix rows the argument uses.
All standard tensor positions are distinct and different from the sign label. -/
theorem one_sign_finrank_le_two (ρ : G →* Module.End K Coeffs) {s : I}
    (hs : SignAt P ρ s) (index : J ↪ I) (away : ∀ j, index j ≠ s)
    (xrow : ∀ (j : J) (f : Coeffs) w, w j = true → ρ (P.x (index j)) f w = -f w)
    (yrow : ∀ (j : J) (f : Coeffs) w, w j = false → ρ (P.y (index j)) f w = -f w) :
    FiniteDimensional.finrank K (HOne ρ) ≤ 2 := by
  let F : HOne ρ →ₗ[K] K × K := endpoints.comp (signMap P hs)
  have ker : LinearMap.ker F = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro c hc
    apply signMap_injective P hs
    rw [map_zero]
    let h := signMap P hs c
    change h = 0
    change (h (fun _ => false), h (fun _ => true)) = (0, 0) at hc
    funext w
    change h w = 0
    classical
    by_cases h0 : w = fun _ => false
    · rw [h0]; exact congrArg Prod.fst hc
    by_cases h1 : w = fun _ => true
    · rw [h1]; exact congrArg Prod.snd hc
    obtain ⟨i, hi⟩ : ∃ i, w i = true := by
      by_contra! hn
      exact h0 (funext fun i => by cases he : w i <;> simp_all)
    obtain ⟨j, hj⟩ : ∃ j, w j = false := by
      by_contra! hn
      exact h1 (funext fun j => by cases he : w j <;> simp_all)
    have hij : index i ≠ index j := by
      intro e
      obtain rfl := index.injective e
      simp [hi] at hj
    have e := congrFun (mixed_difference P hs (away i) (away j) hij c) w
    change ρ (P.y (index j)) (h - ρ (P.x (index i)) h) w =
      h w - ρ (P.x (index i)) h w at e
    rw [yrow _ _ _ hj] at e
    change -(h w - ρ (P.x (index i)) h w) = h w - ρ (P.x (index i)) h w at e
    rw [xrow _ _ _ hi, sub_neg_eq_add] at e
    have sum := cancel_double (K := K) _ (neg_eq_iff_add_eq_zero.mp e)
    exact cancel_double (K := K) _ sum
  have bound := LinearMap.finrank_le_finrank_of_injective (LinearMap.ker_eq_bot.mp ker)
  simpa only [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_self] using bound

end WordCoordinates
end BlockingCurves.CubicCocycles
