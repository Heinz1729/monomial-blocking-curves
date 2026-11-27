import PhaseCharacterOrthogonality
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace BlockingCurves.PiecewiseCharacter

variable {E : Type*} [Field E] [Fintype E]

/-- Embed the multiplicative group in the complex roots of unity and extend by zero. -/
theorem faithful_character : ∃ ψ : MulChar E ℂ, Function.Injective ψ := by
  classical
  let N : ℕ+ := ⟨Fintype.card E-1, Nat.sub_pos_of_lt Fintype.one_lt_card⟩
  have card : Nat.card Eˣ = Nat.card (rootsOfUnity N ℂ) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units,
      Complex.card_rootsOfUnity]
    rfl
  let e : Eˣ ≃* rootsOfUnity N ℂ := mulEquivOfCyclicCardEq card
  let h : Eˣ →* ℂˣ := (rootsOfUnity N ℂ).subtype.comp e.toMonoidHom
  let ψ := MulChar.ofUnitHom h
  have units (u : Eˣ) : ψ (u:E) = (h u:ℂ) := MulChar.ofUnitHom_coe h u
  have nz (x : E) (hx : x ≠ 0) : ψ x ≠ 0 := by
    change ψ ((Units.mk0 x hx : Eˣ) : E) ≠ 0
    rw [units]
    exact Units.ne_zero _
  refine ⟨ψ, fun x y hxy => ?_⟩
  by_cases hx : x=0
  · subst x
    by_contra hy
    exact nz y (Ne.symm hy) (hxy.symm.trans ψ.map_zero)
  by_cases hy : y=0
  · subst y
    exact (nz x hx (hxy.trans ψ.map_zero)).elim
  let u := Units.mk0 x hx
  let v := Units.mk0 y hy
  have eq : h u = h v := Units.ext ((units u).symm.trans (hxy.trans (units v)))
  exact congrArg Units.val (e.injective (Subtype.ext eq))

/-- Complex character of exact order m with exactly the algebraic power-label fibres,
including the distinguished value at zero. -/
theorem exists_power_label_character {m : ℕ} (hm : 0 < m) (dvd : m ∣ Fintype.card E-1) :
    let e := (Fintype.card E-1)/m
    ∃ χ : MulChar E ℂ, orderOf χ = m ∧ ∀ x y : E, χ x = χ y ↔ x^e = y^e := by
  classical
  intro e
  have prod : e*m = Fintype.card E-1 := Nat.div_mul_cancel dvd
  have he : e ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.sub_pos_of_lt Fintype.one_lt_card) dvd) hm).ne'
  obtain ⟨ψ,hψ⟩ := faithful_character (E:=E)
  have full : orderOf ψ = Fintype.card E-1 := by
    apply Nat.dvd_antisymm
    · apply orderOf_dvd_of_pow_eq_one
      simpa only [← Fintype.card_units] using MulChar.pow_card_eq_one ψ
    · obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α:=Eˣ)
      rw [← Fintype.card_units,← orderOf_eq_card_of_forall_mem_zpowers hg]
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      apply hψ
      rw [Units.val_pow_eq_pow_val,map_pow, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
        MulChar.one_apply g.isUnit,Units.val_one,map_one]
  refine ⟨ψ^e,?_, fun x y => ?_⟩
  · rw [orderOf_pow' _ he,full,← prod,Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero he)]
  · rw [MulChar.pow_apply' ψ he, MulChar.pow_apply' ψ he, ← map_pow, ← map_pow]
    exact hψ.eq_iff

end BlockingCurves.PiecewiseCharacter
