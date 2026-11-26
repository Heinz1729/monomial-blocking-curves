import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card

/-! Derangements in a translate of a doubly transitive finite permutation group.
The action need not be faithful. The permutation defining the translate need not normalize it. -/
namespace BlockingCurves.FrobeniusCoset

variable {G X : Type*} [Group G] [MulAction G X]

/-- The sum, over a translate of the group, of its fixed-point counts is |G|.
This bijective first-moment argument is valid for every transitive action. -/
noncomputable def fixedIncidenceEquiv (σ : Equiv.Perm X) (base : X)
    (trans : ∀ x y : X, ∃ g : G, g • x = y) :
    G ≃ {z : G × X // σ (z.1 • z.2) = z.2} := by
  let t (x : X) : G := Classical.choose (trans base (σ.symm x))
  have ht (x : X) : t x • base = σ.symm x := Classical.choose_spec (trans base _)
  refine ⟨fun g => ⟨(t (g • base)*g⁻¹, g • base), ?_⟩,
    fun z => z.val.1⁻¹ * t z.val.2, ?_, ?_⟩
  · simp [mul_smul, ht]
  · intro g
    simp
  · rintro ⟨⟨g, x⟩, hx⟩
    have hx' : g • x = σ.symm x := by
      apply σ.injective
      simpa using hx
    have hbase : (g⁻¹ * t x) • base = x := by simp [mul_smul, ht, ← hx']
    apply Subtype.ext
    change (t ((g⁻¹*t x) • base) * (g⁻¹*t x)⁻¹, (g⁻¹*t x) • base) = (g,x)
    simp [hbase]

/-- Every translate of a group transitive on ordered distinct pairs contains
a fixed-point-free element, also when the translate is the group itself. -/
theorem exists_derangement_of_two_transitive [Finite G] [Nontrivial X]
    (twoTrans : ∀ x y u v : X, x ≠ y → u ≠ v → ∃ g : G, g • x = u ∧ g • y = v)
    (σ : Equiv.Perm X) : ∃ g : G, ∀ x : X, σ (g • x) ≠ x := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have trans : ∀ x y : X, ∃ g : G, g • x = y := by
    intro u v
    obtain ⟨u', hu⟩ := exists_ne u
    obtain ⟨v', hv⟩ := exists_ne v
    obtain ⟨g, hg, _⟩ := twoTrans u u' v v' hu.symm hv.symm
    exact ⟨g, hg⟩
  let I := {z : G × X // σ (z.1 • z.2) = z.2}
  let π : I → G := fun z => z.val.1
  let e : I ≃ G := (fixedIncidenceEquiv σ x trans).symm
  letI : Finite I := Finite.of_equiv G e.symm
  by_contra! hall
  have onto : Function.Surjective π := by
    intro g
    obtain ⟨a, ha⟩ := hall g
    exact ⟨⟨(g,a),ha⟩, rfl⟩
  have inj := (Finite.injective_iff_surjective_of_equiv e).mpr onto
  obtain ⟨g, hu, hv⟩ := twoTrans x y (σ.symm x) (σ.symm y) hxy
    (fun h => hxy (σ.symm.injective h))
  let u : I := ⟨(g,x), by simp [hu]⟩
  let v : I := ⟨(g,y), by simp [hv]⟩
  exact hxy (congrArg (fun i : I => i.val.2) (inj (show π u = π v from rfl)))

end BlockingCurves.FrobeniusCoset
