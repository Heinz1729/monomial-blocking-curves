import CuspidalGeometricLower
import CuspidalConstantLift

/-! Coefficientwise Frobenius on the geometric parameter line fixes its
transcendental parameter and preserves each translated cusp polynomial. -/
namespace BlockingCurves.CuspidalGeneral
open Polynomial
noncomputable section

variable {k : Type*} [Field k]

private def ratCongr (e : k ≃+* k) : RatFunc k ≃+* RatFunc k :=
  IsFractionRing.fieldEquivOfRingEquiv (Polynomial.mapEquiv e)

private theorem ratCongr_poly (e : k ≃+* k) (P : k[X]) :
    ratCongr e (algebraMap k[X] (RatFunc k) P) =
      algebraMap k[X] (RatFunc k) (P.map e) := by
  unfold ratCongr IsFractionRing.fieldEquivOfRingEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

variable (F : Type*) [Field F] [Fintype F]

private theorem exists_coefficientFrobenius :
    ∃ e : RatFunc (AlgebraicClosure F) ≃+* RatFunc (AlgebraicClosure F),
      (∀ c : AlgebraicClosure F, e (RatFunc.C c) = RatFunc.C (c ^ Fintype.card F)) ∧
      e RatFunc.X = RatFunc.X := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card F (ringChar F)
  let K := AlgebraicClosure F
  letI : CharP K (ringChar F) := charP_of_injective_algebraMap' F K _
  letI : ExpChar K (ringChar F) := ExpChar.prime hp
  let e := iterateFrobeniusEquiv K (ringChar F) n
  refine ⟨ratCongr e, ?_, ?_⟩
  · intro c
    have h := ratCongr_poly e (C c)
    simpa only [RatFunc.algebraMap_C, map_C, RingEquiv.coe_toRingHom,
      e, iterateFrobeniusEquiv_def, ← hn] using h
  · simpa only [RatFunc.algebraMap_X, map_X] using ratCongr_poly e X

/-- q-power on geometric constants, with the intercept variable fixed. -/
def coefficientFrobenius := (exists_coefficientFrobenius F).choose

theorem coefficientFrobenius_C (c : AlgebraicClosure F) :
    coefficientFrobenius F (RatFunc.C c) = RatFunc.C (c ^ Fintype.card F) :=
  (exists_coefficientFrobenius F).choose_spec.1 c

theorem coefficientFrobenius_X : coefficientFrobenius F RatFunc.X = RatFunc.X :=
  (exists_coefficientFrobenius F).choose_spec.2

variable {F}

/-- Each coordinate is defined over the original finite field. -/
theorem coefficientFrobenius_coordinate (d : ℕ) (a u : F) :
    (cuspCoordinate d (algebraMap F (AlgebraicClosure F) a)
      (algebraMap F (AlgebraicClosure F) u)).map (coefficientFrobenius F).toRingHom =
    cuspCoordinate d (algebraMap F (AlgebraicClosure F) a) (algebraMap F (AlgebraicClosure F) u) := by
  have hc (v : F) : (coefficientFrobenius F).toRingHom (RatFunc.C (algebraMap F _ v)) =
      RatFunc.C (algebraMap F (AlgebraicClosure F) v) := by
    exact (coefficientFrobenius_C F _).trans (by rw [← map_pow, FiniteField.pow_card])
  have hx : (coefficientFrobenius F).toRingHom RatFunc.X = RatFunc.X :=
    coefficientFrobenius_X F
  simp only [cuspCoordinate, lineFibre, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, map_X, map_C, map_add, hx, hc]

theorem coefficientFrobenius_product (d : ℕ) (a : F) (S : Finset F) :
    let P := ∏ u ∈ geometricShifts S, cuspCoordinate d (algebraMap F (AlgebraicClosure F) a) u
    P.map (coefficientFrobenius F).toRingHom = P := by
  classical
  dsimp only
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro u hu
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hu
  exact coefficientFrobenius_coordinate d a v

/-- Restrict a semilinear field automorphism to the actual roots of an
invariant polynomial. Finiteness turns the resulting injection into a permutation. -/
private def semilinearRoots {B E : Type*} [Field B] [Field E] [Algebra B E]
    (e : B ≃+* B) (g : E ≃+* E)
    (ext : ∀ z : B, g (algebraMap B E z) = algebraMap B E (e z))
    (P : B[X]) (nz : P ≠ 0) (fixed : P.map e.toRingHom = P) : Equiv.Perm (P.rootSet E) := by
  classical
  have comm : (algebraMap B E).comp e.toRingHom = g.toRingHom.comp (algebraMap B E) :=
    RingHom.ext fun z => (ext z).symm
  let send (x : P.rootSet E) : P.rootSet E := ⟨g x.val, (mem_rootSet_of_ne nz).mpr (by
    have eqn := map_aeval_eq_aeval_map comm P x.val
    rw [fixed, (mem_rootSet_of_ne nz).mp x.property, map_zero] at eqn
    exact eqn.symm)⟩
  have inj : Function.Injective send :=
    fun _ _ h => Subtype.ext (g.injective (congrArg Subtype.val h))
  exact Equiv.ofBijective send ⟨inj, Finite.surjective_of_injective inj⟩

/-- A semilinear lift to the actual joint geometric splitting field. -/
def geometricFrobenius (d : ℕ) (a : F) (S : Finset F) :
    GeometricSplitting d a S ≃+* GeometricSplitting d a S :=
  (exists_semilinear_splitting_lift (coefficientFrobenius F) _
    (coefficientFrobenius_product d a S)).choose

theorem geometricFrobenius_extends (d : ℕ) (a : F) (S : Finset F)
    (z : RatFunc (AlgebraicClosure F)) :
    geometricFrobenius d a S (algebraMap _ _ z) =
      algebraMap _ _ (coefficientFrobenius F z) :=
  (exists_semilinear_splitting_lift (coefficientFrobenius F) _
    (coefficientFrobenius_product d a S)).choose_spec z

/-- The arithmetic coset on the geometric field consists of all lifts of
the base automorphism. Changing the chosen lift only reindexes this coset. -/
theorem geometricFrobenius_coset (d : ℕ) (a : F) (S : Finset F)
    (τ : GeometricSplitting d a S ≃+* GeometricSplitting d a S) :
    (∀ z : RatFunc (AlgebraicClosure F), τ (algebraMap _ _ z) =
      algebraMap _ _ (coefficientFrobenius F z)) ↔
    ∃ g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S,
      ∀ x, τ x = geometricFrobenius d a S (g x) := by
  let σ := geometricFrobenius d a S
  constructor
  · intro h
    let g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S :=
      { τ.trans σ.symm with
        commutes' := fun z => by
          change σ.symm (τ (algebraMap _ _ z)) = _
          rw [h, ← geometricFrobenius_extends d a S z]
          exact σ.symm_apply_apply _ }
    exact ⟨g, fun x => (σ.apply_symm_apply (τ x)).symm⟩
  · rintro ⟨g, h⟩ z
    rw [h, g.commutes, geometricFrobenius_extends]

/-- The permutation of the same labelled roots as the geometric group action. -/
def frobeniusRootAction {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (i : S) : Equiv.Perm (Fin d) :=
  let label := rootLabel hd ha S i
  let perm := semilinearRoots (coefficientFrobenius F) (geometricFrobenius d a S)
    (geometricFrobenius_extends d a S) _ (cuspCoordinate_irreducible (by omega) _ _).ne_zero
    (coefficientFrobenius_coordinate d a i.val)
  label.trans (perm.trans label.symm)

theorem frobeniusRootAction_apply {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (i : S) (x : Fin d) :
    (rootLabel hd ha S i (frobeniusRootAction hd ha S i x)).val =
      geometricFrobenius d a S (rootLabel hd ha S i x).val := by
  unfold frobeniusRootAction
  change ((rootLabel hd ha S i) ((rootLabel hd ha S i).symm _)).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- A product in the labelled Frobenius coset is the actual action of the
geometric automorphism followed by the chosen semilinear lift. -/
theorem frobenius_coset_action {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)
    (i : S) (x : Fin d) :
    (rootLabel hd ha S i ((frobeniusRootAction hd ha S * geometricRootAction hd ha S g) i x)).val =
      geometricFrobenius d a S (g (rootLabel hd ha S i x).val) := by
  change (rootLabel hd ha S i (frobeniusRootAction hd ha S i (geometricRootAction hd ha S g i x))).val = _
  rw [frobeniusRootAction_apply, rootLabel_action]

/-- The d!-th iterate fixes every sheet simultaneously. The period bound is
independent of the number of translates, even though the lift still acts
nontrivially on the algebraic closure of the constants. -/
theorem frobenius_iterate_fixes_sheets {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F)
    (g : GeometricSplitting d a S ≃ₐ[RatFunc (AlgebraicClosure F)] GeometricSplitting d a S)
    (i : S) (x : Fin d) :
    (fun y => geometricFrobenius d a S (g y))^[d.factorial] (rootLabel hd ha S i x).val =
      (rootLabel hd ha S i x).val := by
  let perm := (frobeniusRootAction hd ha S * geometricRootAction hd ha S g) i
  let label (v : Fin d) := (rootLabel hd ha S i v).val
  have act : Function.Semiconj label perm (fun y => geometricFrobenius d a S (g y)) :=
    fun v => frobenius_coset_action hd ha S g i v
  have power : perm ^ d.factorial = 1 := by
    simpa only [Fintype.card_perm, Fintype.card_fin] using (pow_card_eq_one (x:=perm))
  have h := act.iterate_right d.factorial x
  rw [Equiv.Perm.iterate_eq_pow, power] at h
  exact h.symm

end
end BlockingCurves.CuspidalGeneral
