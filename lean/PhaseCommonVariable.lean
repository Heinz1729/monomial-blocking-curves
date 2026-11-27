import PhaseBranches

/-! The common intercept and the entire inverse fibre of each cyclotomic branch.
Products are taken in the ordinary polynomial ring before evaluation at a single
normalized Frobenius operator, so their order is immaterial. -/

namespace BlockingCurves.PhaseCommonVariable
open Polynomial Finset
open scoped BigOperators

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

noncomputable def productEnd (T : Module.End F E) (Z : Finset F) : Module.End F E :=
  aeval T (∏ u ∈ Z, (C u * X - 1 : F[X]))

private theorem factor_at (T : Module.End F E) (Z : Finset F) [DecidableEq F]
    {z : F} (hz : z ∈ Z) (t : E) :
    z • T (productEnd T (Z.erase z) t) - productEnd T (Z.erase z) t =
      productEnd T Z t := by
  unfold productEnd
  rw [← Finset.mul_prod_erase Z (fun u => (C u * X - 1 : F[X])) hz]
  simp [LinearMap.mul_apply, Module.algebraMap_end_apply]

noncomputable def normalized (σ : E ≃ₐ[F] E) (a : E) : Module.End F E :=
  a⁻¹ • σ.toLinearEquiv.toLinearMap

/-- The identity holds for singular and invertible branches, including when
the original fibre is empty or contains more than one rational point. -/
theorem candidate_iff (σ : E ≃ₐ[F] E) {a : E} (ha : a ≠ 0) (Z : Finset F)
    [DecidableEq F] {z : F} (hz : z ∈ Z) (t α x : E) :
    let T := normalized σ a
    let Q := productEnd T (Z.erase z) t
    let L := fun y : E => algebraMap F E z * σ y - a*y
    L x = a * productEnd T Z t + α ↔ ∃ c, L c = α ∧ x = Q+c := by
  let T := normalized σ a
  let Q := productEnd T (Z.erase z) t
  let L := fun y : E => algebraMap F E z * σ y - a*y
  change L x = a * productEnd T Z t + α ↔ ∃ c, L c = α ∧ x = Q+c
  have hQ : L Q = a * productEnd T Z t := by
    rw [← factor_at T Z hz t]
    change algebraMap F E z * σ Q - a*Q = a*(z • (a⁻¹ * σ Q) - Q)
    rw [Algebra.smul_def, mul_sub]
    congr 1
    field_simp
  have hL (v w : E) : L (v+w) = L v + L w := by
    dsimp [L]
    rw [map_add]
    ring
  constructor
  · intro hx
    refine ⟨x-Q, ?_, by abel⟩
    have h := hL Q (x-Q)
    rw [show Q+(x-Q)=x by abel, hx, hQ] at h
    exact (add_left_cancel h).symm
  · rintro ⟨c,hc,rfl⟩
    rw [hL, hQ, hc]

/-- A zero of a candidate polynomial determines its shift. In particular,
two different shifts have disjoint zero sets even for singular branches.
The identity works over an algebraic closure with its s-power automorphism. -/
theorem root_determines_shift (σ : E ≃ₐ[F] E) {a : E} (ha : a ≠ 0) (Z : Finset F)
    [DecidableEq F] {z : F} (hz : z ∈ Z) {t c α : E}
    (hc : algebraMap F E z * σ c - a*c = α)
    (root : productEnd (normalized σ a) (Z.erase z) t + c = 0) :
    a*productEnd (normalized σ a) Z t = -α := by
  have h := (candidate_iff σ ha Z hz t α 0).2 ⟨c,hc,root.symm⟩
  simp only [map_zero, mul_zero, sub_self] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- An actual common change of variable for the s-Frobenius, with one
intercept working for every base-field multiplier in Z simultaneously. -/
theorem simultaneous_actual_fibres [Fintype F] [Fintype E] [DecidableEq F]
    {a : E} (ha : a ≠ 0) (Z : Finset F) :
    ∃ σ : E ≃ₐ[F] E, (∀ x, σ x = x^Fintype.card F) ∧
      ∀ z ∈ Z, ∀ t α x : E,
        (algebraMap F E z*x^Fintype.card F-a*x = a*productEnd (normalized σ a) Z t+α ↔
          ∃ c, algebraMap F E z*c^Fintype.card F-a*c = α ∧
            x = productEnd (normalized σ a) (Z.erase z) t+c) := by
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  refine ⟨σ,hσ,?_⟩
  intro z hz t α x
  simpa only [hσ] using candidate_iff σ ha Z hz t α x

/-- Prescribing a nonzero character class different from its branch label
at every candidate gives an actual missing projective line. The quantifier
over c includes every rational point of every singular branch fibre. -/
theorem wrong_classes_miss [Fintype F] [Fintype E] [DecidableEq F] {m n : ℕ}
    (divides : m ∣ Fintype.card F-1) (size : Fintype.card E = Fintype.card F^n)
    (σ : E ≃ₐ[F] E) (hσ : ∀ x : E, σ x = x^Fintype.card F)
    {a : E} (ha : a ≠ 0) (t : E) (S : Set E) :
    let Z := univ.filter (fun z : F => z^m = 1)
    let k := (Fintype.card E-1)/m
    let T := normalized σ a
    (∀ z ∈ Z, ∀ α ∈ S, ∀ c : E, algebraMap F E z*σ c - a*c = α →
      let x := productEnd T (Z.erase z) t + c
      x ≠ 0 ∧ x^k ≠ algebraMap F E z) →
    ¬ProjectiveBlocks (Fintype.card F+k) S := by
  classical
  intro Z k T wrong blocks
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have hd : 2 ≤ Fintype.card F+k := hs.trans_le (Nat.le_add_right _ _)
  let b := a * productEnd T Z t
  obtain ⟨x,hx⟩ := (projectiveBlocks_iff_graphHits hd S).1 blocks a b
  let α := x^(Fintype.card F+k)-a*x-b
  change α ∈ S at hx
  have branch : ∃ z ∈ Z, x^(Fintype.card F+k) = algebraMap F E z*σ x ∧
      (x = 0 ∨ x^k = algebraMap F E z) := by
    by_cases h0 : x = 0
    · subst x
      exact ⟨1,by simp [Z],by simp [zero_pow (by omega : Fintype.card F+k ≠ 0)],Or.inl rfl⟩
    · obtain ⟨z,hz,eq⟩ := ExtensionPhase.cyclotomic_value_in_ground divides size x h0
      have iz : (z:F) ∈ Z := mem_filter.mpr ⟨mem_univ _,by
        simpa using congrArg (fun u : Fˣ => (u:F)) hz⟩
      refine ⟨z,iz,?_,Or.inr eq.symm⟩
      rw [pow_add, hσ,eq,mul_comm]
  obtain ⟨z,hz,eq,alt⟩ := branch
  have hit : algebraMap F E z*σ x - a*x = b+α := by
    dsimp [α]
    rw [eq]
    abel
  obtain ⟨c,hc,xc⟩ := (candidate_iff σ ha Z hz t α x).1 hit
  have exclusion := wrong z hz α hx c hc
  change x = productEnd T (Z.erase z) t + c at xc
  rw [← xc] at exclusion
  exact alt.elim exclusion.1 exclusion.2

/-- A single slope works for every shift set. Counting all rational
candidates, including the entire exceptional kernel, costs at most 2m per
shift in the character expansion. -/
theorem rational_candidate_budget [Fintype F] [Fintype E] [DecidableEq F]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) :
    ∃ a : Eˣ, ∀ S : Finset E,
      ∑ α ∈ S, ∑ z ∈ univ.filter (fun u:Fˣ => u^m=1),
        Nat.card {x:E // algebraMap F E (z:F)*x^Fintype.card F-(a:E)*x=α} ≤ 2*m*S.card := by
  classical
  obtain ⟨a,choice⟩ := ExtensionPhase.primitive_norm_slope hn divides size
  let Z := univ.filter (fun z:Fˣ => z^m=1)
  let L (z : Fˣ) (x : E) := algebraMap F E (z:F)*x^Fintype.card F-(a:E)*x
  let count (α : E) (z : Fˣ) := Nat.card {x:E // L z x=α}
  have zcard : Z.card ≤ m := IsCyclic.card_pow_eq_one_le hm
  have easy {z : Fˣ} (h : Function.Bijective (L z)) (α : E) : count α z ≤ 1 := by
    haveI : Subsingleton {x:E // L z x=α} := ⟨fun x y => Subtype.ext (h.1 (x.2.trans y.2.symm))⟩
    change Nat.card _ ≤ 1
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have per (α : E) : ∑ z ∈ Z, count α z ≤ 2*m := by
    rcases choice with all | ⟨sz,_,z,⟨hz,notGood⟩,unique⟩
    · have h := Finset.sum_le_sum (s := Z) (g := fun _ => 1)
          (fun z hz => easy (all z (mem_filter.mp hz).2) α)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
      exact h.trans (zcard.trans (by omega))
    · let z' := (Units.map (algebraMap F E).toMonoidHom) z
      have noninj : ¬ Function.Injective (L z) := fun hi =>
        notGood ⟨hi,Finite.surjective_of_injective hi⟩
      have normEq := not_not.mp (mt (ExtensionPhase.branch_injective_iff_norm_ne hn size z' a).2 noninj)
      have hc := ExtensionPhase.singular_fibre_card hn size z' a α normEq
      change count α z = 0 ∨ count α z = Fintype.card F at hc
      have hzZ : z ∈ Z := mem_filter.mpr ⟨mem_univ _,hz⟩
      have other (u : Fˣ) (hu : u ∈ Z.erase z) : count α u ≤ 1 := by
        apply easy
        by_contra h
        exact (mem_erase.mp hu).1 (unique u ⟨(mem_filter.mp (mem_erase.mp hu).2).2,h⟩)
      have h := Finset.sum_le_sum (s := Z.erase z) (g := fun _ => 1) other
      simp only [Finset.sum_const,smul_eq_mul,mul_one] at h
      rw [← Finset.sum_erase_add _ _ hzZ]
      rw [card_erase_of_mem hzZ] at h
      have hp := card_pos.mpr ⟨z,hzZ⟩
      have hc' : count α z ≤ Fintype.card F := by rcases hc with h0 | hs <;> omega
      exact (Nat.add_le_add h hc').trans (by omega)
  refine ⟨a,fun S => ?_⟩
  have bound := Finset.sum_le_sum (s := S) (g := fun _ => 2*m) (fun α _ => per α)
  simpa only [Finset.sum_const,smul_eq_mul,Nat.mul_comm S.card] using bound

end BlockingCurves.PhaseCommonVariable
