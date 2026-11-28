import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators

/-! A coset of a doubly transitive group contains a derangement. No restriction
on the order of an inertia group or on the characteristic enters the count. -/
namespace BlockingCurves.CuspidalGeneral

open Finset
open scoped BigOperators

/-- A normal subgroup containing the inertia at a fibre of orbit sizes
one and d-1 is doubly transitive in a transitive degree-d action, d ≥ 3. -/
theorem normal_pair_transport {G X : Type*} [Group G] [Fintype X] [MulAction G X]
    (hd : 2 < Fintype.card X) (N : Subgroup G) (normal : N.Normal)
    (trans : ∀ x u : X, ∃ g : G, g • x=u) (x₀ : X)
    (own : ∀ y z : X, y≠x₀ → z≠x₀ → ∃ n ∈ N, n • x₀=x₀ ∧ n • y=z) :
    ∀ x y u v : X, x≠y → u≠v → ∃ g ∈ N, g • x=u ∧ g • y=v := by
  classical
  have stabilizer (u y z : X) (hy : y≠u) (hz : z≠u) :
      ∃ n ∈ N, n • u=u ∧ n • y=z := by
    obtain ⟨g,rfl⟩ := trans x₀ u
    have away (y : X) (h : y≠g • x₀) : g⁻¹ • y≠x₀ := by
      intro e
      exact h (by rw [←e,smul_inv_smul])
    obtain ⟨n,hn,fix,move⟩ := own (g⁻¹ • y) (g⁻¹ • z) (away _ hy) (away _ hz)
    exact ⟨g*n*g⁻¹,normal.conj_mem n hn g, by simp [mul_smul,fix],
      by simp [mul_smul,move]⟩
  intro x y u v hxy huv
  obtain ⟨w,hw⟩ : ∃ w : X, w ∉ ({x,u}:Finset X) := by
    by_contra! h
    have full := eq_univ_of_forall h
    have small : ({x,u}:Finset X).card ≤ 2 := card_le_two
    rw [full,card_univ] at small
    omega
  simp only [mem_insert,mem_singleton,not_or] at hw
  obtain ⟨a,ha,_,ax⟩ := stabilizer w x u (Ne.symm hw.1) (Ne.symm hw.2)
  have ay : a • y≠u := by
    rw [←ax,ne_eq,smul_left_cancel_iff]
    exact hxy.symm
  obtain ⟨b,hb,bu,byv⟩ := stabilizer u (a • y) v ay huv.symm
  exact ⟨b*a,N.mul_mem hb ha,by rw [mul_smul,ax,bu],by rw [mul_smul,byv]⟩

/-- Point transport gives equal row sizes in the incidence matrix of a
permutation coset. Pair transport supplies a member with two fixed points. -/
theorem coset_derangement {G X : Type*} [Group G] [Fintype G] [Fintype X]
    [Nontrivial X] [MulAction G X]
    (pairs : ∀ x y u v : X, x≠y → u≠v → ∃ g : G, g • x=u ∧ g • y=v)
    (σ : Equiv.Perm X) : ∃ g : G, ∀ x : X, σ (g • x)≠x := by
  classical
  have trans (x u : X) : ∃ g : G, g • x=u := by
    obtain ⟨y,hy⟩ := exists_ne x
    obtain ⟨v,hv⟩ := exists_ne u
    obtain ⟨g,hg,_⟩ := pairs x y u v hy.symm hv.symm
    exact ⟨g,hg⟩
  let row (x y : X) := univ.filter (fun g : G => g • x=y)
  have same (x y z : X) : (row x y).card=(row x z).card := by
    obtain ⟨u,hu⟩ := trans y z
    apply card_bij (fun g _ => u*g)
    · intro g hg
      exact mem_filter.mpr ⟨mem_univ _,by rw [mul_smul,(mem_filter.mp hg).2,hu]⟩
    · intro a _ b _ h
      exact mul_left_cancel h
    · intro g hg
      refine ⟨u⁻¹*g,mem_filter.mpr ⟨mem_univ _,?_⟩,by simp⟩
      rw [mul_smul,(mem_filter.mp hg).2,←hu,inv_smul_smul]
  have balance (x : X) : Fintype.card X*(row x (σ.symm x)).card=Fintype.card G := by
    calc
      _ = ∑ _y : X, (row x (σ.symm x)).card := by simp
      _ = ∑ y : X, (row x y).card := sum_congr rfl (fun y _ => same x _ y)
      _ = _ := by
        dsimp [row]
        rw [← card_eq_sum_card_fiberwise (fun g (_ : g∈(univ:Finset G)) => mem_univ (g • x)),card_univ]
  let fix (g : G) := univ.filter (fun x : X => g • x=σ.symm x)
  have swap : ∑ g : G, (fix g).card=∑ x : X, (row x (σ.symm x)).card := by
    simp only [fix,row,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  have total : ∑ g : G, (fix g).card=Fintype.card G := by
    apply Nat.eq_of_mul_eq_mul_left (Fintype.card_pos (α:=X))
    rw [swap,mul_sum]
    simp [balance]
  by_contra! all
  have one (g : G) : 1 ≤ (fix g).card := by
    obtain ⟨x,h⟩ := all g
    exact card_pos.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,(σ.apply_eq_iff_eq_symm_apply).mp h⟩⟩
  obtain ⟨x,y,xy⟩ := exists_pair_ne X
  obtain ⟨g,hx,hy⟩ := pairs x y (σ.symm x) (σ.symm y) xy (σ.symm.injective.ne xy)
  have two : 1 < (fix g).card :=
    one_lt_card_iff.mpr ⟨x,y,mem_filter.mpr ⟨mem_univ _,hx⟩,mem_filter.mpr ⟨mem_univ _,hy⟩,xy⟩
  have strict : ∑ _ : G, 1 < ∑ u : G, (fix u).card :=
    sum_lt_sum (fun u _ => one u) ⟨g,mem_univ _,two⟩
  simp [total] at strict

/-- Transitive coordinate projections together with inertia supported at a
single coordinate suffice to adjust an arbitrary arithmetic permutation tuple.
The hypotheses describe the geometric action at the separated branch values. -/
theorem independent_inertia_derangements {I X : Type*} [Fintype I] [Fintype X]
    [Nontrivial X] (hd : 2 < Fintype.card X) (H : Subgroup (I → Equiv.Perm X))
    (trans : ∀ i x u, ∃ h : H, (h.val i) x=u)
    (inertia : ∀ i, ∃ x₀ : X, ∀ y z : X, y≠x₀ → z≠x₀ →
      ∃ h : H, (∀ j, j≠i → h.val j=1) ∧ (h.val i) x₀=x₀ ∧ (h.val i) y=z)
    (σ : I → Equiv.Perm X) : ∃ h : H, ∀ i x, σ i (h.val i x)≠x := by
  classical
  have coordinate (i : I) (τ : Equiv.Perm X) : ∃ h : H,
      (∀ j, j≠i → h.val j=1) ∧ ∀ x, τ (h.val i x)≠x := by
    let Hact : H →* Equiv.Perm X := (Pi.evalMonoidHom (fun _ : I => Equiv.Perm X) i).comp H.subtype
    letI : MulAction H X := MulAction.compHom X Hact
    let N : Subgroup H :=
      { carrier := {h | ∀ j, j≠i → h.val j=1}
        one_mem' := fun _ _ => rfl
        mul_mem' := by
          intro a b ha hb j hj
          change a.val j*b.val j=1
          rw [ha j hj,hb j hj,one_mul]
        inv_mem' := by
          intro a ha j hj
          change (a.val j)⁻¹=1
          rw [ha j hj,inv_one] }
    have norm : N.Normal := by
      constructor
      intro n hn g j hj
      change g.val j*n.val j*(g.val j)⁻¹=1
      rw [show n.val j=1 from hn j hj,mul_one,mul_right_inv]
    obtain ⟨x₀,localInertia⟩ := inertia i
    have own (y z : X) (hy : y≠x₀) (hz : z≠x₀) :
        ∃ h ∈ N, h • x₀=x₀ ∧ h • y=z := by
      obtain ⟨h,away,fix,move⟩ := localInertia y z hy hz
      exact ⟨h,away,fix,move⟩
    have pairs (x y u v : X) (hxy : x≠y) (huv : u≠v) :
        ∃ g : N, g • x=u ∧ g • y=v := by
      obtain ⟨g,hg,first,second⟩ := normal_pair_transport hd N norm (trans i) x₀ own x y u v hxy huv
      exact ⟨⟨g,hg⟩,first,second⟩
    letI : Fintype H := Fintype.ofFinite H
    letI : Fintype N := Fintype.ofFinite N
    obtain ⟨g,none⟩ := coset_derangement pairs τ
    exact ⟨g.val,g.property,none⟩
  have assemble (S : Finset I) : ∃ h : H, ∀ i ∈ S, ∀ x, σ i (h.val i x)≠x := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1,by simp⟩
    | @insert i S hi ih =>
      obtain ⟨h,old⟩ := ih
      obtain ⟨k,away,none⟩ := coordinate i (σ i*h.val i)
      refine ⟨h*k,?_⟩
      intro j hj x
      rcases mem_insert.mp hj with rfl | hold
      · exact none x
      · change σ j (h.val j ((k.val j) x))≠x
        rw [away j (fun e => hi (e ▸ hold))]
        exact old j hold x
  obtain ⟨h,good⟩ := assemble univ
  exact ⟨h,fun i => good i (mem_univ i)⟩

end BlockingCurves.CuspidalGeneral
