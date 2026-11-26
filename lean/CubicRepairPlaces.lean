import CubicAlteration
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.Valuation.ValuationSubring

/-! Common cubic function fields and specialization at rational places (§17). -/
namespace BlockingCurves.CubicRepairPlaces
open CubicAlteration IntermediateField
universe u

structure Branch (F : Type u) [Field F] (R : Finset (Line F)) where
  K : Type u
  [fieldK : Field K]
  [algebraK : Algebra (RatFunc F) K]
  root : R → K
  equation : ∀ i, (root i)^3 =
    algebraMap (RatFunc F) K (RatFunc.C (i.val.1:F)) * root i +
    algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C i.val.2)
  generated : IntermediateField.adjoin (RatFunc F) (Set.range root) = ⊤

attribute [instance] Branch.fieldK Branch.algebraK

variable {F : Type u} [Field F] {R : Finset (Line F)}

noncomputable def constant (D : Branch F R) : F →+* D.K :=
  (algebraMap (RatFunc F) D.K).comp RatFunc.C

noncomputable def parameter (D : Branch F R) : D.K := algebraMap (RatFunc F) D.K RatFunc.X

/-- A rational place is represented by its valuation ring and its residue map,
with the base field fixed. -/
structure Place (D : Branch F R) where
  ring : ValuationSubring D.K
  constants : ∀ a : F, constant D a ∈ ring
  residue : ring →+* F
  on_constants : ∀ a : F, residue ⟨constant D a, constants a⟩ = a

/-- A root of X³−mX−c over a valuation ring has no pole if m and c have none. -/
theorem root_regular {K : Type*} [Field K] (O : ValuationSubring K) {x m c : K}
    (hm : m ∈ O) (hc : c ∈ O) (he : x^3 = m*x+c) : x ∈ O := by
  by_contra hn
  have hx : x ≠ 0 := fun hz => hn (hz ▸ O.zero_mem)
  have hi := (O.mem_or_inv_mem x).resolve_left hn
  have eq : x = m*x⁻¹+c*(x⁻¹)^2 := by
    calc
      x = (m*x+c)/x^2 := (eq_div_iff (pow_ne_zero _ hx)).2 (by linear_combination he)
      _ = _ := by field_simp [hx]; ring
  apply hn
  rw [eq]
  exact add_mem (mul_mem hm hi) (mul_mem hc (pow_mem hi 2))

/-- Reducing the simultaneous cubics at an actual nonpolar rational place
supplies one common parameter and rational roots for all residual lines. -/
theorem hit_of_regular_place (D : Branch F R) (p : Place D) (h : parameter D ∈ p.ring) :
    ∃ a : F, ∀ l ∈ R, Hits a l := by
  let A : p.ring := ⟨parameter D,h⟩
  let C (a : F) : p.ring := ⟨constant D a,p.constants a⟩
  refine ⟨p.residue A, ?_⟩
  intro l hl
  let i : R := ⟨l,hl⟩
  have he : (D.root i)^3 = constant D (l.1:F)*D.root i + (parameter D + constant D l.2) := by
    simpa [i, constant, parameter] using D.equation i
  have hx := root_regular p.ring (p.constants (l.1:F)) (add_mem h (p.constants l.2)) he
  let X : p.ring := ⟨D.root i,hx⟩
  have e : X^3 = C (l.1:F)*X + (A+C l.2) := by
    apply Subtype.ext
    change p.ring.toSubring.subtype (X^3) = p.ring.toSubring.subtype (C (l.1:F)*X + (A+C l.2))
    simpa only [map_pow, map_mul, map_add] using he
  have er := congrArg p.residue e
  simp only [map_pow, map_add, map_mul, C, p.on_constants] at er
  exact ⟨p.residue X, by linear_combination er⟩


private theorem map_ratfunc_mem {E : Type*} [Field E] (g : RatFunc F →+* E) (T : Subfield E)
    (hc : ∀ a : F, g (RatFunc.C a) ∈ T) (hx : g RatFunc.X ∈ T) (t : RatFunc F) :
    g t ∈ T := by
  have pol (p : Polynomial F) : g (algebraMap (Polynomial F) _ p) ∈ T := by
    induction p using Polynomial.induction_on' with
    | h_add p q hp hq => simpa only [map_add] using T.add_mem hp hq
    | h_monomial n a =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, map_mul, map_pow,
        RatFunc.algebraMap_C, RatFunc.algebraMap_X]
      exact T.mul_mem (hc a) (T.pow_mem hx _)
  apply RatFunc.induction_on t
  intro p q _
  rw [map_div₀]
  exact T.div_mem (pol p) (pol q)

/-- Each one-root stage is a rational function field, by an isomorphism fixing
every coefficient. The new generator x recovers the old parameter as x³−mx−b. -/
theorem single_root_rational (D : Branch F R) (i : R) :
    ∃ e : RatFunc F ≃+* adjoin (RatFunc F) {D.root i},
      ∀ c : F, (e (RatFunc.C c) : D.K) = constant D c := by
  classical
  letI : Algebra F D.K := (constant D).toAlgebra
  letI : IsScalarTower F (RatFunc F) D.K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι := algebraMap (RatFunc F) D.K
  have ht : Transcendental F (parameter D) := by
    have eqn : Polynomial.aeval (parameter D) =
        (IsScalarTower.toAlgHom F (RatFunc F) D.K).comp
          (IsScalarTower.toAlgHom F (Polynomial F) (RatFunc F)) := by
      apply Polynomial.algHom_ext
      simp [parameter]
    intro halg
    apply isAlgebraic_iff_not_injective.mp halg
    rw [eqn]
    exact ι.injective.comp (IsFractionRing.injective (Polynomial F) (RatFunc F))
  have he : parameter D = (D.root i)^3 - constant D (i.val.1:F)*D.root i - constant D i.val.2 := by
    have h := D.equation i
    rw [map_add] at h
    dsimp [parameter,constant]
    linear_combination -h
  have hx : Transcendental F (D.root i) := by
    intro ha
    apply ht
    rw [he]
    have hc (a : F) : IsIntegral F (constant D a) := isIntegral_algebraMap
    exact (((ha.isIntegral.pow 3).sub ((hc _).mul ha.isIntegral)).sub (hc _)).isAlgebraic
  have hi : Function.Injective (Polynomial.aeval (D.root i) : Polynomial F →ₐ[F] D.K) := by
    by_contra h
    exact hx (isAlgebraic_iff_not_injective.mpr h)
  let g := RatFunc.liftAlgHom (Polynomial.aeval (D.root i))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)
  have hX : g RatFunc.X = D.root i := by simp [g,RatFunc.liftAlgHom_apply]
  have hC (a : F) : g (RatFunc.C a) = constant D a := g.commutes a
  let T := adjoin (RatFunc F) {D.root i}
  have inside (t : RatFunc F) : g t ∈ T := by
    apply map_ratfunc_mem g.toRingHom T.toSubfield _ _ t
    · intro a
      change g (RatFunc.C a) ∈ T
      rw [hC]
      exact T.algebraMap_mem _
    · change g RatFunc.X ∈ T
      rw [hX]
      exact subset_adjoin _ _ (Set.mem_singleton _)
  have rootMem : D.root i ∈ g.fieldRange := ⟨_,hX⟩
  have constMem (a : F) : constant D a ∈ g.fieldRange := ⟨_,hC a⟩
  have paramMem : parameter D ∈ g.fieldRange := by
    rw [he]
    exact sub_mem (sub_mem (pow_mem rootMem _) (mul_mem (constMem _) rootMem)) (constMem _)
  have hbase (t : RatFunc F) : ι t ∈ g.fieldRange :=
    map_ratfunc_mem ι g.fieldRange.toSubfield constMem paramMem t
  let E' : IntermediateField (RatFunc F) D.K := g.fieldRange.toSubfield.toIntermediateField hbase
  have hT : T ≤ E' := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr rootMem)
  let f : RatFunc F →+* T := g.toRingHom.codRestrict T.toSubring inside
  have fj : Function.Surjective f := by
    intro t
    obtain ⟨r,hr⟩ := AlgHom.mem_fieldRange.mp (hT t.property)
    exact ⟨r,Subtype.ext hr⟩
  exact ⟨RingEquiv.ofBijective f ⟨f.injective,fj⟩,hC⟩

end BlockingCurves.CubicRepairPlaces
