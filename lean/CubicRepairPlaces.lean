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

noncomputable abbrev baseConstant (F K : Type*) [Field F] [Field K] [Algebra (RatFunc F) K] : F →+* K :=
  (algebraMap (RatFunc F) K).comp RatFunc.C

noncomputable abbrev constant (D : Branch F R) : F →+* D.K := baseConstant F D.K

noncomputable def parameter (D : Branch F R) : D.K := algebraMap (RatFunc F) D.K RatFunc.X

/-- A rational place is represented by its valuation ring and its residue map,
with the base field fixed. -/
structure RationalPlace (F K : Type*) [Field F] [Field K] [Algebra (RatFunc F) K] where
  ring : ValuationSubring K
  constants : ∀ a : F, baseConstant F K a ∈ ring
  residue : ring →+* F
  on_constants : ∀ a : F, residue ⟨baseConstant F K a, constants a⟩ = a

abbrev Place (D : Branch F R) := RationalPlace F D.K

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

/-- If a transcendental rational parameter is a polynomial in x, adjoining x
produces the rational field F(x). The isomorphism respects the coefficient field. -/
theorem rational_single_of_power_equation {K : Type*} [Field K] [Algebra (RatFunc F) K]
    (x : K) (d h : ℕ) (m b : F)
    (equation : x^d = algebraMap (RatFunc F) K (RatFunc.C m)*x^h +
      algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C b)) :
    ∃ e : RatFunc F ≃+* adjoin (RatFunc F) {x},
      ∀ c : F, (e (RatFunc.C c) : K) = algebraMap (RatFunc F) K (RatFunc.C c) := by
  classical
  let ψ := (algebraMap (RatFunc F) K).comp (RatFunc.C : F →+* RatFunc F)
  letI : Algebra F K := ψ.toAlgebra
  letI : IsScalarTower F (RatFunc F) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ι := algebraMap (RatFunc F) K
  let t := ι RatFunc.X
  have ht : Transcendental F t := by
    have eqn : Polynomial.aeval t = (IsScalarTower.toAlgHom F (RatFunc F) K).comp
          (IsScalarTower.toAlgHom F (Polynomial F) (RatFunc F)) := by
      apply Polynomial.algHom_ext
      simp [t,ι]
    intro halg
    apply isAlgebraic_iff_not_injective.mp halg
    rw [eqn]
    exact ι.injective.comp (IsFractionRing.injective (Polynomial F) (RatFunc F))
  have he : t = x^d - ψ m*x^h - ψ b := by
    rw [map_add] at equation
    dsimp [t,ι,ψ]
    linear_combination -equation
  have hx : Transcendental F x := by
    intro ha
    apply ht
    rw [he]
    have hc (a : F) : IsIntegral F (ψ a) := isIntegral_algebraMap
    exact (((ha.isIntegral.pow d).sub ((hc _).mul (ha.isIntegral.pow h))).sub (hc _)).isAlgebraic
  have hi : Function.Injective (Polynomial.aeval x : Polynomial F →ₐ[F] K) := by
    by_contra h
    exact hx (isAlgebraic_iff_not_injective.mpr h)
  let g := RatFunc.liftAlgHom (Polynomial.aeval x)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)
  have hX : g RatFunc.X = x := by simp [g,RatFunc.liftAlgHom_apply]
  have hC (a : F) : g (RatFunc.C a) = ψ a := g.commutes a
  let T := adjoin (RatFunc F) {x}
  have inside (t : RatFunc F) : g t ∈ T := by
    apply map_ratfunc_mem g.toRingHom T.toSubfield _ _ t
    · intro a
      change g (RatFunc.C a) ∈ T
      rw [hC]
      exact T.algebraMap_mem _
    · change g RatFunc.X ∈ T
      rw [hX]
      exact subset_adjoin _ _ (Set.mem_singleton _)
  have rootMem : x ∈ g.fieldRange := ⟨_,hX⟩
  have constMem (a : F) : ψ a ∈ g.fieldRange := ⟨_,hC a⟩
  have paramMem : t ∈ g.fieldRange := by
    rw [he]
    exact sub_mem (sub_mem (pow_mem rootMem _) (mul_mem (constMem _) (pow_mem rootMem _))) (constMem _)
  have hbase (t : RatFunc F) : ι t ∈ g.fieldRange :=
    map_ratfunc_mem ι g.fieldRange.toSubfield constMem paramMem t
  let E' : IntermediateField (RatFunc F) K := g.fieldRange.toSubfield.toIntermediateField hbase
  have hT : T ≤ E' := adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr rootMem)
  let f : RatFunc F →+* T := g.toRingHom.codRestrict T.toSubring inside
  have fj : Function.Surjective f := by
    intro t
    obtain ⟨r,hr⟩ := AlgHom.mem_fieldRange.mp (hT t.property)
    exact ⟨r,Subtype.ext hr⟩
  exact ⟨RingEquiv.ofBijective f ⟨f.injective,fj⟩,hC⟩

/-- The graph-pencil specialization has a linear term in the root. -/
theorem rational_single_of_equation {K : Type*} [Field K] [Algebra (RatFunc F) K]
    (x : K) (d : ℕ) (m b : F)
    (equation : x^d = algebraMap (RatFunc F) K (RatFunc.C m)*x +
      algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C b)) :
    ∃ e : RatFunc F ≃+* adjoin (RatFunc F) {x},
      ∀ c : F, (e (RatFunc.C c) : K) = algebraMap (RatFunc F) K (RatFunc.C c) :=
  rational_single_of_power_equation x d 1 m b (by simpa using equation)

/-- The one-root stage of the common cubic branch is rational over the original base field. -/
theorem single_root_rational (D : Branch F R) (i : R) :
    ∃ e : RatFunc F ≃+* adjoin (RatFunc F) {D.root i},
      ∀ c : F, (e (RatFunc.C c) : D.K) = constant D c :=
  rational_single_of_equation (D.root i) 3 _ _ (D.equation i)

end BlockingCurves.CubicRepairPlaces
