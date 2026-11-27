import MainResult
import Mathlib.FieldTheory.Finite.GaloisField

namespace BlockingCurves

open Polynomial

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [Fintype K] [Fintype E]

/-- Raising to the order of the base field is an automorphism of a finite extension. -/
theorem exists_card_frobenius :
    ∃ σ : E ≃ₐ[K] E, ∀ x : E, σ x = x ^ Fintype.card K := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  letI : CharP E (ringChar K) := charP_of_injective_algebraMap' K E _
  letI : ExpChar E (ringChar K) := ExpChar.prime hp
  let f : E →ₐ[K] E :=
    { toRingHom := iterateFrobenius E (ringChar K) n
      commutes' := by
        intro k
        change (algebraMap K E k) ^ (ringChar K) ^ (n : ℕ) = algebraMap K E k
        rw [← hn, ← map_pow, FiniteField.pow_card] }
  have hi : Function.Injective f := f.toRingHom.injective
  refine ⟨AlgEquiv.ofBijective f ⟨hi, Finite.surjective_of_injective hi⟩, ?_⟩
  intro x
  change x ^ (ringChar K) ^ (n : ℕ) = x ^ Fintype.card K
  rw [hn]

/-- The only elements fixed by the relative Frobenius are scalars. -/
theorem pow_card_eq_iff_scalar (x : E) :
    x ^ Fintype.card K = x ↔ ∃ k : K, algebraMap K E k = x := by
  classical
  constructor
  · intro hx
    let P : K[X] := X ^ Fintype.card K - X
    have hdeg : Multiset.card P.roots = P.natDegree := by
      rw [show P = X ^ Fintype.card K - X from rfl, FiniteField.roots_X_pow_card_sub_X,
        FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card]
      exact Finset.card_univ
    have hr := Polynomial.roots_map_of_injective_of_card_eq_natDegree
      (algebraMap K E).injective hdeg
    have hx' : x ∈ (P.map (algebraMap K E)).roots := by
      simp only [P, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
      apply (Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero E Fintype.one_lt_card)).2
      simp [Polynomial.IsRoot, hx]
    rw [← hr, Multiset.mem_map] at hx'
    obtain ⟨k, _, hk⟩ := hx'
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    rw [← map_pow, FiniteField.pow_card]

/-- Exact minimum for the graph of the relative Frobenius, with no fixed-field hypothesis. -/
theorem relative_frobenius_minimum [FiniteDimensional K E] :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧
      GraphHits (fun x : E => x ^ Fintype.card K) (S : Set E)}
      ((Fintype.card K - 1) * FiniteDimensional.finrank K E + 1) := by
  obtain ⟨σ, hσ⟩ := exists_card_frobenius K E
  have hfix (x : E) : σ x = x ↔ ∃ k : K, algebraMap K E k = x := by
    rw [hσ]
    exact pow_card_eq_iff_scalar K E x
  have he : (σ : E → E) = fun x => x ^ Fintype.card K := funext hσ
  simpa only [he] using exact_graph_minimum σ hfix

#print axioms relative_frobenius_minimum

end BlockingCurves

namespace BlockingCurves
open Polynomial
variable {K E : Type*} [Field K] [Fintype K] [Field E] [Fintype E] [Algebra K E]
  [FiniteDimensional K E]

theorem power_apply_formula (σ : E ≃ₐ[K] E)
    (hσ : ∀ x : E, σ x = x ^ Fintype.card K) (j : ℕ) (x : E) :
    (σ ^ j) x = x ^ Fintype.card K ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ, pow_mul]
    change σ ((σ ^ j) x) = _
    rw [hσ, ih]

theorem relative_order (σ : E ≃ₐ[K] E)
    (hσ : ∀ x : E, σ x = x ^ Fintype.card K) :
    orderOf σ = FiniteDimensional.finrank K E := by
  classical
  let q := Fintype.card K
  let n := FiniteDimensional.finrank K E
  have hq : 1 < q := Fintype.one_lt_card
  have hn : 0 < n := FiniteDimensional.finrank_pos
  have hcard : Fintype.card E = q ^ n := card_eq_pow_finrank
  have hpow : σ ^ n = 1 := by
    ext x
    change (σ ^ n) x = x
    rw [power_apply_formula σ hσ, ← hcard]
    exact FiniteField.pow_card x
  apply le_antisymm (orderOf_le_of_pow_eq_one hn hpow)
  apply (Nat.pow_le_pow_iff_right hq).mp
  rw [← hcard]
  let m := orderOf σ
  have hm : 0 < m := orderOf_pos σ
  have hqm : 1 < q ^ m := Nat.one_lt_pow (Nat.ne_of_gt hm) hq
  let P : E[X] := X ^ (q ^ m) - X
  have allRoots : (Finset.univ : Finset E).val ⊆ P.roots := by
    intro x _
    apply (Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero E hqm)).2
    have he := power_apply_formula σ hσ m x
    have hz : σ ^ m = 1 := pow_orderOf_eq_one σ
    rw [hz] at he
    change x = x ^ q ^ m at he
    simp [Polynomial.IsRoot,P,← he]
  have bound := Polynomial.card_le_degree_of_subset_roots allRoots
  simpa only [Finset.card_univ, P, FiniteField.X_pow_card_sub_X_natDegree_eq E hqm] using bound

/-- All Frobenius iterates, with the numerical size of the fixed subfield made explicit. -/
theorem iterated_frobenius_minimum (j : ℕ) :
    let n := FiniteDimensional.finrank K E
    let g := n.gcd j
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧
      GraphHits (fun x : E => x ^ (Fintype.card K ^ j)) (S : Set E)}
      ((Fintype.card K ^ g - 1) * (n / g) + 1) := by
  classical
  let n := FiniteDimensional.finrank K E
  let g := n.gcd j
  obtain ⟨σ, hσ⟩ := exists_card_frobenius K E
  let τ := σ ^ j
  let H := Subgroup.zpowers τ
  let L := IntermediateField.fixedField H
  letI : Fintype L := Fintype.ofFinite L
  have gen : τ ∈ H := Subgroup.mem_zpowers τ
  have hmem (x : E) : x ∈ L ↔ τ x = x := by
    constructor
    · intro hx
      exact hx ⟨τ,gen⟩
    · intro hx
      have hle : H ≤ MulAction.stabilizer (E ≃ₐ[K] E) x :=
        Subgroup.zpowers_le_of_mem hx
      intro a
      exact hle a.property
  let φ : E ≃ₐ[L] E := { τ.toRingEquiv with commutes' := fun k => (hmem k).mp k.property }
  have hfix (x : E) : φ x = x ↔ ∃ k : L, algebraMap L E k = x := by
    change τ x = x ↔ _
    rw [← hmem]
    exact ⟨fun hx => ⟨⟨x,hx⟩,rfl⟩, fun ⟨k,hk⟩ => hk ▸ k.property⟩
  have hdeg : FiniteDimensional.finrank L E = n / g := by
    rw [IntermediateField.finrank_fixedField_eq_card H]
    change Fintype.card ↥(Subgroup.zpowers (σ ^ j)) = n / g
    rw [Fintype.card_zpowers, orderOf_pow, relative_order σ hσ]
  have hsize : Fintype.card L = Fintype.card K ^ g := by
    rw [card_eq_pow_finrank (K := K) (V := L)]
    congr 1
    have ht := FiniteDimensional.finrank_mul_finrank K L E
    rw [hdeg] at ht
    have hc : (n / g) * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n j)
    have hnd : 0 < n / g := hdeg ▸ FiniteDimensional.finrank_pos
    exact Nat.mul_right_cancel hnd (ht.trans (by simpa [Nat.mul_comm] using hc.symm))
  have he : (φ : E → E) = fun x => x ^ (Fintype.card K ^ j) :=
    funext (power_apply_formula σ hσ j)
  simpa only [he, hsize, hdeg] using exact_graph_minimum φ hfix

#print axioms iterated_frobenius_minimum



/-- Prime-power form: over the field with p^h elements all exponents p^e are covered,
including the cases when the map is the identity. -/
theorem prime_power_frobenius_minimum (p h e : ℕ) [Fact p.Prime] (hh : h ≠ 0) :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField p h), S.card = r ∧
      GraphHits (fun x : GaloisField p h => x ^ (p ^ e)) (S : Set (GaloisField p h))}
      ((p ^ (h.gcd e) - 1) * (h / h.gcd e) + 1) := by
  simpa only [ZMod.card, GaloisField.finrank p hh] using
    (iterated_frobenius_minimum (K := ZMod p) (E := GaloisField p h) e)

#print axioms prime_power_frobenius_minimum

end BlockingCurves