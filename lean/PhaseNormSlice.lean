import Frobenius

/-! Separating the conjugate roots on a fixed-direction base-field line.
Every collision of distinct affine linear maps is empty or is a coset of a
proper kernel, so fewer than |F| ordered pairs can be avoided simultaneously. -/

namespace BlockingCurves.PhaseNormSlice
open Finset

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Fintype F] [Fintype E]
noncomputable local instance : DecidableEq E := Classical.decEq _

theorem affine_fibre_bound (A : E →ₗ[F] E) (nonzero : A ≠ 0) (w : E) :
    (univ.filter (fun x : E => A x = w)).card * Fintype.card F ≤ Fintype.card E := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, A v ≠ 0 := by
    by_contra! h
    exact nonzero (LinearMap.ext (by simpa using h))
  let U := univ.filter (fun x : E => A x = w)
  let pack (p : U × F) : E := p.1.val + p.2 • v
  have inj : Function.Injective pack := by
    rintro ⟨x,c⟩ ⟨y,d⟩ h
    change x.val + c • v = y.val + d • v at h
    have hx : A x.val = w := (mem_filter.mp x.property).2
    have hy : A y.val = w := (mem_filter.mp y.property).2
    have ha := congrArg A h
    simp only [map_add, map_smul, hx, hy, add_right_inj] at ha
    have hcd : c = d := by
      have hz : (c-d) • A v = 0 := by rw [sub_smul, ha, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hv)
    subst d
    have hxy : x = y := Subtype.ext (add_right_cancel h)
    subst y
    rfl
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective pack inj

/-- For fixed direction, A i is the linear part of the normalized root and
b i its shift. Distinct affine maps with the same linear part never collide. -/
theorem exists_separating_slice {ι : Type*} [Fintype ι] (A : ι → E →ₗ[F] E) (b : ι → E)
    (distinct : ∀ i j, i ≠ j → A i ≠ A j ∨ b i ≠ b j)
    (room : Fintype.card ι^2 < Fintype.card F) :
    ∃ u : E, Function.Injective (fun i => A i u + b i) := by
  classical
  let s := Fintype.card F
  let q := Fintype.card E
  let bad (p : ι × ι) := univ.filter (fun u : E =>
    p.1 ≠ p.2 ∧ A p.1 u + b p.1 = A p.2 u + b p.2)
  have one (p : ι × ι) : (bad p).card ≤ q/s := by
    apply (Nat.le_div_iff_mul_le Fintype.card_pos).2
    by_cases h : p.1 = p.2
    · simp [bad,h]
    by_cases hA : A p.1 = A p.2
    · have hb := (distinct p.1 p.2 h).resolve_left (not_not.mpr hA)
      have hempty : bad p = ∅ := by
        apply eq_empty_iff_forall_not_mem.mpr
        intro x hx
        have heq := (mem_filter.mp hx).2.2
        rw [hA] at heq
        exact hb (add_left_cancel heq)
      simp [hempty]
    · have he : bad p ⊆ univ.filter (fun x : E => (A p.1-A p.2) x = b p.2 - b p.1) := by
        intro x hx
        obtain ⟨_,eq⟩ := (mem_filter.mp hx).2
        apply mem_filter.mpr ⟨mem_univ _,?_⟩
        simp only [LinearMap.sub_apply]
        linear_combination eq
      exact (Nat.mul_le_mul_right s (card_le_card he)).trans
        (affine_fibre_bound _ (sub_ne_zero.mpr hA) _)
  let U := (univ : Finset (ι × ι)).biUnion bad
  have upper : U.card ≤ Fintype.card ι^2 * (q/s) := by
    simpa [U,Fintype.card_prod,pow_two] using
      card_biUnion_le_card_mul (univ : Finset (ι × ι)) bad (q/s) (fun p _ => one p)
  have small : U.card < q := by
    by_cases hz : q/s = 0
    · rw [hz,mul_zero] at upper
      exact lt_of_le_of_lt upper Fintype.card_pos
    · exact upper.trans_lt ((Nat.mul_lt_mul_of_pos_right room (Nat.pos_of_ne_zero hz)).trans_le
        ((Nat.mul_comm s (q/s)) ▸ Nat.div_mul_le_self q s))
  obtain ⟨u,hu⟩ : ∃ u : E, u ∉ U := by
    by_contra! full
    rw [eq_univ_of_forall full,card_univ] at small
    exact (Nat.lt_irrefl _) small
  refine ⟨u,?_⟩
  intro i j h
  by_contra ne
  exact hu (mem_biUnion.mpr ⟨(i,j),mem_univ _,mem_filter.mpr ⟨mem_univ _,ne,h⟩⟩)

/-- Any fixed nonzero direction v suffices. Normalization at v identifies
proportional operators. Repeated operators with different shifts have no
common root on the slice. -/
theorem conjugate_roots_separate {ι : Type*} [Fintype ι] (U : ι → E ≃ₗ[F] E)
    (shift : ι → E) {v : E} (hv : v ≠ 0)
    (pairs : ∀ i j, i ≠ j →
      (¬ ∃ c : E, ∀ x : E, U i x = c * U j x) ∨ (U i = U j ∧ shift i ≠ shift j))
    (room : Fintype.card ι^2 < Fintype.card F) :
    ∃ u : E, Function.Injective (fun i => -(U i (u+shift i) / U i v)) := by
  let A (i : ι) : E →ₗ[F] E := (U i v)⁻¹ • (U i).toLinearMap
  let b (i : ι) := A i (shift i)
  have nz (i : ι) : U i v ≠ 0 := by simpa using hv
  have key (i : ι) (x : E) : A i x = U i x / U i v := by
    change (U i v)⁻¹ * U i x = _
    rw [div_eq_mul_inv,mul_comm]
  have diff (i j : ι) (hij : i ≠ j) : A i ≠ A j ∨ b i ≠ b j := by
    rcases pairs i j hij with np | ⟨e,h⟩
    · left
      intro h
      apply np
      refine ⟨U i v / U j v, fun x => ?_⟩
      have hx := congrArg (fun f : E →ₗ[F] E => f x) h
      change A i x = A j x at hx
      rw [key,key] at hx
      field_simp [nz i,nz j] at hx ⊢
      linear_combination hx
    · right
      intro eq
      apply h
      change A i (shift i) = A j (shift j) at eq
      rw [key,key,e] at eq
      exact (U j).injective ((div_left_inj' (nz j)).mp eq)
  obtain ⟨u,hu⟩ := exists_separating_slice A b diff room
  refine ⟨u,?_⟩
  intro i j he
  apply hu
  change A i u + A i (shift i) = A j u + A j (shift j)
  rw [← map_add, ← map_add,key,key]
  exact neg_inj.mp he

end BlockingCurves.PhaseNormSlice
