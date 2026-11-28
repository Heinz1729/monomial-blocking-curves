import CuspidalGeneralLower
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-! Inertia on the roots of the cusp pencil, using the valuation ring of the
splitting field and its residue homomorphism. The simple-root argument holds
for arbitrary inertia, including wild inertia. -/
namespace BlockingCurves.CuspidalGeneral

open Polynomial

/-- Monicity puts every root in the valuation ring of the ambient field. -/
theorem monic_root_mem_valuation {L : Type*} [Field L] (A : ValuationSubring L)
    {P : A[X]} (hP : P.Monic) {x : L} (root : aeval x P = 0) : x ∈ A := by
  have h : IsIntegral A x := ⟨P,hP,root⟩
  obtain ⟨y,rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral h
  exact y.property

/-- Two roots with equal reduction over a domain coincide if that reduction
is a simple root. No Henselian or ramification hypothesis is needed. -/
theorem eq_of_common_simple_reduction {R k : Type*} [CommRing R] [IsDomain R]
    [Field k] (ρ : R →+* k) {P : R[X]} {x y : R} (hx : P.eval x = 0)
    (hy : P.eval y = 0) (same : ρ x = ρ y) (simple : ρ (P.derivative.eval x) ≠ 0) :
    x = y := by
  by_contra ne
  obtain ⟨Q,hQ⟩ := (dvd_iff_isRoot.mpr hx : X - C x ∣ P)
  have qy : Q.eval y = 0 := by
    rw [hQ,eval_mul,eval_sub,eval_X,eval_C] at hy
    exact (mul_eq_zero.mp hy).resolve_left (sub_ne_zero.mpr (Ne.symm ne))
  apply simple
  rw [hQ,derivative_mul]
  simpa only [derivative_sub,derivative_X,derivative_C,sub_zero,one_mul,
    eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero] using
    (show ρ (Q.eval x)=0 by
      rw [←eval₂_at_apply,same,eval₂_at_apply,qy,map_zero])

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Elements of Mathlib's inertia group fix the reduction of every integral
element. The automorphisms are those of the ambient field extension. -/
theorem inertia_residue_eq (A : ValuationSubring L) (g : A.inertiaSubgroup K) (x : A) :
    LocalRing.residue A (g.val • x) = LocalRing.residue A x := by
  rw [LocalRing.ResidueField.residue_smul]
  have h := g.property
  change MulSemiringAction.toRingAut (A.decompositionSubgroup K) (LocalRing.ResidueField A) g.val = 1 at h
  exact congrArg (fun σ : RingAut (LocalRing.ResidueField A) => σ (LocalRing.residue A x)) h

/-- Integral model of a cusp fibre over a coefficient ring. -/
noncomputable def integralFibre {R : Type*} [CommRing R] (d : ℕ) (a v : R) : R[X] :=
  X^d - (C a * X^(d-1) + C v)

theorem integralFibre_monic {R : Type*} [CommRing R] [IsDomain R]
    {d : ℕ} (hd : 2 ≤ d) (a v : R) : (integralFibre d a v).Monic := by
  obtain ⟨n,rfl⟩ : ∃ n, d=n+1 := ⟨d-1,by omega⟩
  unfold integralFibre
  apply monic_X_pow_sub
  apply degree_add_le_of_degree_le
  · by_cases h : a = 0
    · simp [h]
    · simp [degree_C_mul h]
  · exact degree_C_le.trans <| WithBot.coe_le_coe.mpr (Nat.zero_le _)

/-- At a noncritical residue value of the cusp polynomial, every element
of the actual inertia group fixes every root in the ambient extension. Both
coefficients lift scalars in the base field. -/
theorem inertia_fixes_regular_fibre (A : ValuationSubring L) {d : ℕ} (hd : 3 ≤ d)
    (a v : A) (a₀ v₀ : K) (la : (a:L)=algebraMap K L a₀) (lv : (v:L)=algebraMap K L v₀)
    (ha : LocalRing.residue A a ≠ 0) (hv : LocalRing.residue A v ≠ 0)
    (avoid : let c := ((d-1:ℕ):LocalRing.ResidueField A)/(d:LocalRing.ResidueField A)
             LocalRing.residue A v ≠ (c^d-c^(d-1))*(LocalRing.residue A a)^d)
    (g : A.inertiaSubgroup K) {x : L} (root : x^d-(a:L)*x^(d-1)=(v:L)) :
    g.val.val x = x := by
  let P := integralFibre d a v
  have px : aeval x P = 0 := by
    simp only [P,integralFibre,map_sub,map_add,map_pow,map_mul,aeval_C,aeval_X,
      ValuationSubring.algebraMap_apply]
    linear_combination root
  let z : A := ⟨x,monic_root_mem_valuation A (integralFibre_monic (by omega) a v) px⟩
  have rz : z^d-a*z^(d-1)=v := Subtype.ext root
  have evalz : P.eval z = 0 := by
    simp only [P,integralFibre,eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C]
    linear_combination rz
  have rmove := congrArg g.val.val root
  simp only [map_sub,map_pow,map_mul,la,lv,AlgEquiv.commutes] at rmove
  have evalgz : P.eval (g.val • z) = 0 := by
    apply Subtype.ext
    simp only [P,integralFibre,eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C]
    change (g.val.val x)^d-((a:L)*(g.val.val x)^(d-1)+(v:L))=0
    rw [la,lv]
    linear_combination rmove
  have simple : LocalRing.residue A (P.derivative.eval z) ≠ 0 := by
    intro bad
    let ρ := LocalRing.residue A
    have br : (ρ z)^d-(ρ a)*(ρ z)^(d-1)=ρ v := by
      simpa only [map_sub,map_pow,map_mul] using congrArg ρ rz
    have bad' : ((X^d-C (ρ a)*X^(d-1)): (LocalRing.ResidueField A)[X]).derivative.eval (ρ z)=0 := by
      change ρ (P.derivative.eval z)=0 at bad
      rw [←eval₂_at_apply,←eval_map,←derivative_map] at bad
      simpa only [P,integralFibre,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_mul,
        Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,derivative_sub,derivative_add,
        derivative_C,add_zero] using bad
    rcases critical_value_cases hd (ρ a) (ρ z) ha bad' with h | h
    · exact hv (br.symm.trans h)
    · exact avoid (br.symm.trans h)
  exact congrArg Subtype.val (eq_of_common_simple_reduction (LocalRing.residue A)
    evalz evalgz (inertia_residue_eq A g z).symm simple).symm

section FunctionField

variable {k : Type*} [Field k]

/-- One translated cover over the rational function field in the intercept. -/
noncomputable def cuspCoordinate (d : ℕ) (a u : k) : (RatFunc k)[X] :=
  lineFibre d (RatFunc.C a) (RatFunc.X + RatFunc.C u)

/-- The compositum realized as the splitting field of the product of the
translated cusp polynomials. -/
noncomputable abbrev cuspCompositum (d : ℕ) (a : k) (S : Finset k) :=
  (∏ u ∈ S, cuspCoordinate d a u).SplittingField

/-- A valuation ring above the finite intercept b = -u: constants have
their given lifts and the rational parameter specializes to -u. -/
structure CuspPlace {M : Type*} [Field M] [Algebra (RatFunc k) M]
    (A : ValuationSubring M) (u : k) where
  constants : k →+* A
  constants_lift : ∀ c, (constants c : M) = algebraMap (RatFunc k) M (RatFunc.C c)
  parameter : A
  parameter_lift : (parameter : M) = algebraMap (RatFunc k) M RatFunc.X
  specializes : LocalRing.residue A parameter = -(LocalRing.residue A (constants u))

/-- The possible nonzero critical value, with the same field casts in
wild characteristic as in `critical_value_cases`. -/
def extraCritical (d : ℕ) (a : k) : k :=
  let c := ((d-1:ℕ):k)/(d:k)
  (c^d-c^(d-1))*a^d

/-- At the zero fibre of u, a distinct separated coordinate v is fixed
pointwise on its splitting roots by every inertia element at that place. -/
theorem inertia_fixes_other_roots {M : Type*} [Field M] [Algebra (RatFunc k) M]
    {d : ℕ} (hd : 3 ≤ d) {a u v : k} (ha : a ≠ 0)
    (apart : Disjoint ({-u,extraCritical d a-u} : Set k) {-v,extraCritical d a-v})
    (A : ValuationSubring M) (place : CuspPlace A u) (g : A.inertiaSubgroup (RatFunc k))
    {x : M} (hx : x ∈ (cuspCoordinate d a v).rootSet M) : g.val.val x = x := by
  let ρ := (LocalRing.residue A).comp place.constants
  let shift := place.parameter + place.constants v
  have vne : v-u ≠ 0 := by
    intro h
    have e := sub_eq_zero.mp h
    exact (Set.disjoint_left.mp apart (by simp : -u ∈ ({-u,extraCritical d a-u} : Set k)))
      (by simp [e])
  have away : v-u ≠ extraCritical d a := by
    intro h
    apply (Set.disjoint_left.mp apart (by simp : -u ∈ ({-u,extraCritical d a-u} : Set k)))
    exact Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (by linear_combination h))
  have reduction : LocalRing.residue A shift = ρ (v-u) := by
    rw [map_sub]
    change LocalRing.residue A (place.parameter + place.constants v) =
      LocalRing.residue A (place.constants v) - LocalRing.residue A (place.constants u)
    rw [map_add,place.specializes]
    ring
  have lift : (shift:M) = algebraMap (RatFunc k) M (RatFunc.X + RatFunc.C v) := by
    change (place.parameter:M)+(place.constants v:M)=_
    rw [place.parameter_lift,place.constants_lift,map_add]
  have evalx := (mem_rootSet.mp hx).2
  simp only [cuspCoordinate,lineFibre,map_sub,map_add,map_mul,map_pow,aeval_X,aeval_C] at evalx
  apply inertia_fixes_regular_fibre A hd (place.constants a) shift (RatFunc.C a)
    (RatFunc.X+RatFunc.C v) (place.constants_lift a) lift
  · exact (map_ne_zero ρ).mpr ha
  · rw [reduction]
    exact (map_ne_zero ρ).mpr vne
  · change LocalRing.residue A shift ≠ extraCritical d (ρ a)
    rw [reduction]
    have comm : ρ (extraCritical d a) = extraCritical d (ρ a) := by
      simp only [extraCritical,map_mul,map_sub,map_pow,map_div₀,map_natCast]
    rw [←comm]
    exact ρ.injective.ne away
  · rw [place.constants_lift,lift,map_add]
    linear_combination evalx

/-- In the actual joint splitting field, at each separated zero branch
the entire inertia group acts trivially in every other coordinate. -/
theorem compositum_inertia_support {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0)
    (S : Finset k) (separated : ∀ u ∈ S, ∀ v ∈ S, u ≠ v →
      Disjoint ({-u,extraCritical d a-u} : Set k) {-v,extraCritical d a-v})
    {u : k} (hu : u ∈ S) (A : ValuationSubring (cuspCompositum d a S))
    (place : CuspPlace A u) (g : A.inertiaSubgroup (RatFunc k)) :
    ∀ v ∈ S, v ≠ u → ∀ x ∈ (cuspCoordinate d a v).rootSet (cuspCompositum d a S),
      g.val.val x = x := by
  intro v hv ne x hx
  exact inertia_fixes_other_roots hd ha (separated u hu v hv ne.symm) A place g hx

/-- Inertia acts trivially on the whole root-generated field of each other
coordinate, not just on its abstract set of labels. -/
theorem inertia_fixes_other_coordinate_field {M : Type*} [Field M] [Algebra (RatFunc k) M]
    {d : ℕ} (hd : 3 ≤ d) {a u v : k} (ha : a ≠ 0)
    (apart : Disjoint ({-u,extraCritical d a-u} : Set k) {-v,extraCritical d a-v})
    (A : ValuationSubring M) (place : CuspPlace A u) (g : A.inertiaSubgroup (RatFunc k))
    {x : M} (hx : x ∈ IntermediateField.adjoin (RatFunc k) ((cuspCoordinate d a v).rootSet M)) :
    g.val.val x = x := by
  apply IntermediateField.adjoin_induction (RatFunc k) (p := fun z => g.val.val z = z) hx
  · exact fun _ hz => inertia_fixes_other_roots hd ha apart A place g hz
  · exact g.val.val.commutes
  · intro x y hx hy
    rw [map_add,hx,hy]
  · intro x hx
    rw [map_neg,hx]
  · intro x hx
    rw [map_inv₀,hx]
  · intro x y hx hy
    rw [map_mul,hx,hy]

end FunctionField

end BlockingCurves.CuspidalGeneral
