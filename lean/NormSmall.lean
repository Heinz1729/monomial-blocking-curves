import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Scalar trace/norm targets in the small quadratic cases. -/
namespace BlockingCurves.NormPencil

/-- For every prescribed pencil value and scaled norm there is a norm
parameter for which the trace/norm quadratic has at most one ground-field root. -/
def ScalarWitness (F : Type*) [Field F] (m : ℕ) : Prop :=
  ∀ t j : F, j ≠ 0 → ∃ v : F, ∀ x y : F,
    x^2+(t-v^m)*x+j*v=0 → y^2+(t-v^m)*y+j*v=0 → x=y

private theorem quadratic_unique {F : Type*} [Field F] {A B : F}
    (hn : ∀ u : F, u ≠ 0 → u^2 ≠ A^2-4*B) {x y : F}
    (hx : x^2+A*x+B=0) (hy : y^2+A*y+B=0) : x=y := by
  by_contra h
  have he : (x-y)*(x+y+A)=0 := by linear_combination hx-hy
  have hs := (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr h)
  apply hn (x-y) (sub_ne_zero.mpr h)
  linear_combination 4*hx-(x+y+A+2*(x-y))*hs

/-- Splitting off one exponent preserves the value at zero while reducing
the remaining exponent modulo the order of the group of units. -/
private theorem reduce_power {F : Type*} [Field F] [Fintype F] {s : ℕ}
    (hsize : Fintype.card F=s) (v : F) (a : ℕ) :
    v^(a%(s-1)+1) = v^(a+1) := by
  by_cases hv : v=0
  · simp [hv]
  · have ho : v^(s-1)=1 := by rw [← hsize]; exact FiniteField.pow_card_sub_one_eq_one v hv
    rw [pow_succ, pow_succ v a]
    congr 1
    calc
      v^(a%(s-1)) = v^(a%(s-1) + (s-1)*(a/(s-1))) := by
        rw [pow_add,pow_mul,ho,one_pow,mul_one]
      _ = _ := congrArg (v ^ ·) (Nat.mod_add_div _ _)

/-- Certificate domain: exponents are reduced to 1,...,s−1. The tested
discriminant condition permits a double root and excludes every nonzero square. -/
def ScalarCheck (F : Type*) [Field F] (s : ℕ) : Prop :=
  ∀ a : Fin (s-1), ∀ t j : F, j ≠ 0 → ∃ v : F, ∀ u : F,
    u ≠ 0 → u^2 ≠ (t-v^(a.val+1))^2-4*(j*v)

theorem scalarWitness_of_check {F : Type*} [Field F] [Fintype F] {s : ℕ}
    (hs : Fintype.card F=s) (hc : ScalarCheck F s) {m : ℕ} (hm : 0<m) :
    ScalarWitness F m := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  intro t j hj
  have hs1 := Fintype.one_lt_card (α := F)
  obtain ⟨v,hv⟩ := hc ⟨a%(s-1),Nat.mod_lt _ (by omega)⟩ t j hj
  rw [reduce_power hs v a] at hv
  exact ⟨v,fun _ _ hx hy => quadratic_unique hv hx hy⟩

/-- Transport a scalar certificate to any model of the same finite field. -/
theorem scalarWitness_transport {F E : Type*} [Field F] [Field E] (e : F ≃+* E)
    {m : ℕ} (h : ScalarWitness F m) : ScalarWitness E m := by
  intro t j hj
  have hn : e.symm j ≠ 0 := by simpa using hj
  obtain ⟨v,hv⟩ := h (e.symm t) (e.symm j) hn
  refine ⟨e v, fun x y hx hy => e.symm.injective (hv _ _ ?_ ?_)⟩
  · simpa using congrArg e.symm hx
  · simpa using congrArg e.symm hy

end BlockingCurves.NormPencil
