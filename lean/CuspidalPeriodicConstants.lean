import CuspidalGeometricFrobenius
import Mathlib.FieldTheory.Finite.GaloisField

/-! The finite coefficient field used to descend a periodic action on roots. -/
namespace BlockingCurves.CuspidalDescent
open Polynomial
noncomputable section
variable (F : Type*) [Field F] [Fintype F]

/-- The coefficient homomorphism on the algebraic closure, iterated r times. -/
theorem exists_constantPower (r : ℕ) :
    ∃ φ : AlgebraicClosure F →+* AlgebraicClosure F, ∀ z, φ z = z^(Fintype.card F)^r := by
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  letI : CharP (AlgebraicClosure F) (ringChar F) := charP_of_injective_algebraMap' F _ _
  letI : ExpChar (AlgebraicClosure F) (ringChar F) := ExpChar.prime hp
  refine ⟨iterateFrobenius _ (ringChar F) (n*r),?_⟩
  intro z
  change z ^ (ringChar F)^(n.val*r) = _
  rw [pow_mul, ←hn]

/-- The copy of the q^r-element field inside the geometric constants. -/
def periodicConstants (r : ℕ) : Subfield (AlgebraicClosure F) :=
  (exists_constantPower F r).choose.eqLocusField (RingHom.id _)

theorem mem_periodicConstants (r : ℕ) (c : AlgebraicClosure F) :
    c ∈ periodicConstants F r ↔ c^(Fintype.card F)^r = c := by
  change (exists_constantPower F r).choose c = c ↔ _
  rw [(exists_constantPower F r).choose_spec]

private def periodicRoots (r : ℕ) (hr : 0 < r) :
    periodicConstants F r ≃ (X^(Fintype.card F)^r-X : F[X]).rootSet (AlgebraicClosure F) := by
  refine Equiv.setCongr ?_
  ext z
  change z ∈ periodicConstants F r ↔ _
  rw [mem_periodicConstants, mem_rootSet_of_ne (FiniteField.X_pow_card_pow_sub_X_ne_zero F
    (Nat.ne_of_gt hr) Fintype.one_lt_card)]
  simp only [map_sub, map_pow, aeval_X, sub_eq_zero]

theorem periodicConstants_card (r : ℕ) (hr : 0 < r) :
    Nat.card (periodicConstants F r) = (Fintype.card F)^r := by
  classical
  let P := (X^(Fintype.card F)^r-X : F[X])
  have hp : ringChar F ∣ Fintype.card F := by
    obtain ⟨n,_,hn⟩ := FiniteField.card F (ringChar F)
    rw [hn]
    exact dvd_pow (dvd_refl _) n.pos.ne'
  rw [Nat.card_congr (periodicRoots F r hr), Nat.card_eq_fintype_card]
  exact (card_rootSet_eq_natDegree (K := AlgebraicClosure F) (p:=P)
    (galois_poly_separable (ringChar F) _ (dvd_pow hp hr.ne'))
    (IsAlgClosed.splits_codomain P)).trans
    (FiniteField.X_pow_card_pow_sub_X_natDegree_eq F hr.ne' Fintype.one_lt_card)

/-- A constant with exactly r distinct conjugates under the q-power map. -/
theorem exists_periodic_constant (r : ℕ) (hr : 0 < r) :
    ∃ θ : AlgebraicClosure F, θ ^ (Fintype.card F)^r = θ ∧
      Function.Injective (fun i : Fin r => θ ^ (Fintype.card F)^i.val) := by
  classical
  let K := periodicConstants F r
  letI : Fintype K := Fintype.ofEquiv _ (periodicRoots F r hr).symm
  obtain ⟨t,gen⟩ := IsCyclic.exists_generator (α := Kˣ)
  let q := Fintype.card F
  have card : Fintype.card K = q^r := (Nat.card_eq_fintype_card).symm.trans
    (periodicConstants_card F r hr)
  have ord : orderOf t = q^r - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers gen, Fintype.card_units, card]
  refine ⟨(t.val : AlgebraicClosure F), (mem_periodicConstants F r _).mp t.val.property, ?_⟩
  intro i j eq
  by_cases small : r=1
  · apply Fin.ext
    have := i.isLt
    have := j.isLt
    omega
  have hq : 1 < q := Fintype.one_lt_card
  have bound (v : Fin r) : q^v.val < orderOf t := by
    rw [ord]
    by_cases hz : v.val = 0
    · have h' := Nat.pow_lt_pow_right hq (by omega : 1 < r)
      simp only [hz, pow_zero, pow_one] at *
      omega
    · have up : q^(v.val+1) ≤ q^r := Nat.pow_le_pow_right hq.le (by omega)
      have one : 1 < q^v.val := Nat.one_lt_pow hz hq
      rw [pow_succ] at up
      have two := Nat.mul_le_mul_left (q^v.val) (show 2 ≤ q from hq)
      omega
  have powers : t^(q^i.val) = t^(q^j.val) := Units.ext (Subtype.ext eq)
  exact Fin.ext ((Nat.pow_right_injective hq)
    (pow_injOn_Iio_orderOf (bound i) (bound j) powers))

end
end BlockingCurves.CuspidalDescent
