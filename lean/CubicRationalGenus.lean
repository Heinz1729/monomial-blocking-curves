import Mathlib.RingTheory.Kaehler
import Mathlib.RingTheory.IntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.FieldTheory.Adjoin

/-! The geometric genus as the dimension of rational Kähler differentials
regular on every normal affine model. On a one-variable function field these
are the affine charts of its nonsingular complete curve. For a rational
function field its two polynomial charts already have zero intersection. -/
noncomputable section
namespace BlockingCurves.CubicRationalGenus

open Polynomial IntermediateField KaehlerDifferential
universe u
variable {F K : Type u} [Field F] [Field K] [Algebra F K]

/-- A normal affine model of the function field, given by its coefficient
algebra, inclusion into the generic field and the fraction-field condition. -/
structure Chart (F K : Type u) [Field F] [Field K] [Algebra F K] where
  A : Type u
  [ringA : CommRing A]
  [domainA : IsDomain A]
  [algebraA : Algebra F A]
  [finiteType : Algebra.FiniteType F A]
  [normal : IsIntegrallyClosed A]
  toField : A →ₐ[F] K
  injective : Function.Injective toField
  generates : IntermediateField.adjoin F (Set.range toField) = ⊤

attribute [instance] Chart.ringA Chart.domainA Chart.algebraA Chart.finiteType Chart.normal

/-- The image of the affine regular forms, written as finite sums of a db. -/
def chartForms (C : Chart F K) : Submodule F (KaehlerDifferential F K) :=
  Submodule.span F {w | ∃ a b : C.A, w = C.toField a • D F K (C.toField b)}

/-- Restriction from the affine chart to its generic point, using mathlib's
canonical map on Kähler differentials. -/
def genericRestriction (C : Chart F K) :
    KaehlerDifferential F C.A →ₗ[F] KaehlerDifferential F K := by
  letI : Algebra C.A K := C.toField.toRingHom.toAlgebra
  letI : IsScalarTower F C.A K := IsScalarTower.of_algebraMap_eq fun c => (C.toField.commutes c).symm
  exact (KaehlerDifferential.map F F C.A K).restrictScalars F

theorem chartForms_eq_range (C : Chart F K) :
    chartForms C = LinearMap.range (genericRestriction C) := by
  letI : Algebra C.A K := C.toField.toRingHom.toAlgebra
  letI : IsScalarTower F C.A K := IsScalarTower.of_algebraMap_eq fun c => (C.toField.commutes c).symm
  let f := KaehlerDifferential.map F F C.A K
  have scale (a : C.A) (w : KaehlerDifferential F K) : a • w = C.toField a • w := by
    exact (algebraMap_smul K a w).symm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,b,rfl⟩
    refine ⟨a • D F C.A b, ?_⟩
    change f (a • D F C.A b) = _
    rw [map_smul, scale]
    exact congrArg (fun v => C.toField a • v) (map_D F F C.A K b)
  · rintro _ ⟨w,rfl⟩
    have hin : w ∈ Submodule.span C.A (Set.range (D F C.A)) := by
      rw [span_range_derivation]; trivial
    change f w ∈ chartForms C
    refine Submodule.span_induction (p := fun v => ∀ a : C.A, C.toField a • f v ∈ chartForms C)
      hin ?_ ?_ ?_ ?_ 1 |> (by simpa using ·)
    · rintro _ ⟨b,rfl⟩ a
      exact Submodule.subset_span ⟨a,b,congrArg (fun v => C.toField a • v) (map_D F F C.A K b)⟩
    · intro a
      simp
    · intro v w hv hw a
      rw [map_add,smul_add]
      exact (chartForms C).add_mem (hv a) (hw a)
    · intro c v hv a
      rw [map_smul, scale, smul_smul, ← map_mul]
      exact hv (a*c)

/-- Global regular differentials inside the differentials of the function field. -/
def regularForms (F K : Type u) [Field F] [Field K] [Algebra F K] :
    Submodule F (KaehlerDifferential F K) :=
  ⨅ C : Chart F K, chartForms C

/-- Geometric genus, measured by the dimension of the regular differentials. -/
def genus (F K : Type u) [Field F] [Field K] [Algebra F K] : ℕ :=
  FiniteDimensional.finrank F (regularForms F K)

private theorem affine_embeds (e : RatFunc F ≃ₐ[F] K) :
    Function.Injective (aeval (e RatFunc.X) : F[X] →ₐ[F] K) := by
  have h : aeval (e RatFunc.X) = e.toAlgHom.comp (IsScalarTower.toAlgHom F F[X] (RatFunc F)) := by
    apply Polynomial.algHom_ext
    simp [RatFunc.algebraMap_X]
  rw [h]
  exact e.injective.comp (IsFractionRing.injective F[X] (RatFunc F))

private theorem affine_generates (e : RatFunc F ≃ₐ[F] K) (t : K)
    (hx : ∀ E : IntermediateField F K, t ∈ E → e RatFunc.X ∈ E) :
    IntermediateField.adjoin F (Set.range (aeval t : F[X] →ₐ[F] K)) = ⊤ := by
  let E := IntermediateField.adjoin F (Set.range (aeval t : F[X] →ₐ[F] K))
  have ht : t ∈ E := subset_adjoin F _ ⟨Polynomial.X, aeval_X t⟩
  have poly (p : F[X]) : e (algebraMap F[X] (RatFunc F) p) ∈ E := by
    induction p using Polynomial.induction_on' with
    | h_add p q hp hq => simpa only [map_add] using E.add_mem hp hq
    | h_monomial n a =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        map_mul, map_pow, show e (RatFunc.C a) = algebraMap F K a from e.commutes a]
      exact E.mul_mem (E.algebraMap_mem a) (pow_mem (hx E ht) n)
  apply eq_top_iff.mpr
  intro k _
  obtain ⟨r,rfl⟩ := e.surjective k
  apply RatFunc.induction_on r
  intro p q _
  rw [map_div₀]
  exact E.div_mem (poly p) (poly q)

private def polynomialChart (t : K) (hi : Function.Injective (aeval t : F[X] →ₐ[F] K))
    (hg : IntermediateField.adjoin F (Set.range (aeval t : F[X] →ₐ[F] K)) = ⊤) : Chart F K where
  A := F[X]
  toField := aeval t
  injective := hi
  generates := hg

private theorem polynomial_form {w : KaehlerDifferential F K} (t : K) (hi hg)
    (hw : w ∈ chartForms (polynomialChart t hi hg)) :
    ∃ p : F[X], w = aeval t p • D F K t := by
  change w ∈ Submodule.span F {v | ∃ a b : F[X], v = aeval t a • D F K (aeval t b)} at hw
  refine Submodule.span_induction (p := fun v => ∃ p : F[X], v = aeval t p • D F K t) hw ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨a,b,rfl⟩ := hv
    exact ⟨a*derivative b,by rw [Derivation.map_aeval, map_mul, smul_smul]⟩
  · exact ⟨0,by simp⟩
  · intro v w hv hw
    obtain ⟨a,rfl⟩ := hv
    obtain ⟨b,rfl⟩ := hw
    exact ⟨a+b,by rw [map_add,add_smul]⟩
  · intro a v hv
    obtain ⟨b,rfl⟩ := hv
    exact ⟨C a*b,by rw [map_mul, aeval_C, ← smul_smul, algebraMap_smul]⟩

private theorem inv_X_degree : (RatFunc.X⁻¹ : RatFunc F).intDegree = -1 := by
  have h := RatFunc.intDegree_mul (RatFunc.X_ne_zero (K := F)) (inv_ne_zero RatFunc.X_ne_zero)
  rw [mul_inv_cancel RatFunc.X_ne_zero, RatFunc.intDegree_one, RatFunc.intDegree_X] at h
  omega

private theorem inv_polynomial_degree (p : F[X]) :
    (aeval (RatFunc.X⁻¹ : RatFunc F) p).intDegree ≤ 0 := by
  let V : Subring (RatFunc F) := {
    carrier := {r | r.intDegree ≤ 0}
    zero_mem' := by simp
    one_mem' := by simp
    neg_mem' := by intro x hx; simpa using hx
    add_mem' := by
      intro x y hx hy
      change (x+y).intDegree ≤ 0
      by_cases hz : x+y=0
      · simp [hz]
      by_cases ht : y=0
      · simpa [ht] using hx
      exact (RatFunc.intDegree_add_le ht hz).trans (max_le hx hy)
    mul_mem' := by
      intro x y hx hy
      change (x*y).intDegree ≤ 0
      by_cases h : x=0 ∨ y=0
      · rcases h with h|h <;> simp [h]
      rw [RatFunc.intDegree_mul (fun h' => h (Or.inl h')) (fun h' => h (Or.inr h'))]
      exact add_nonpos hx hy }
  change aeval (RatFunc.X⁻¹ : RatFunc F) p ∈ V
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq => simpa only [map_add] using V.add_mem hp hq
  | h_monomial n a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_X, aeval_C]
    apply V.mul_mem
    · exact (RatFunc.intDegree_C a).le
    · apply V.pow_mem
      exact (inv_X_degree (F := F)).trans_le (by norm_num)

/-- The actual rational Kähler differentials regular in both polynomial charts
vanish, over any field and in every characteristic. -/
theorem regularForms_eq_bot (e : RatFunc F ≃ₐ[F] K) : regularForms F K = ⊥ := by
  let x := e RatFunc.X
  have hi := affine_embeds e
  have hj : Function.Injective (aeval x⁻¹ : F[X] →ₐ[F] K) := by
    by_contra hn
    exact (isAlgebraic_iff_not_injective.mp (IsAlgebraic.inv_iff.mp (isAlgebraic_iff_not_injective.mpr hn))) hi
  have hU := affine_generates e x (fun _ h => h)
  have hV := affine_generates e x⁻¹ (fun E h => by simpa [x] using E.inv_mem h)
  apply eq_bot_iff.mpr
  intro w hw
  change w = 0
  rw [regularForms, Submodule.mem_iInf] at hw
  obtain ⟨p,hp⟩ := polynomial_form x hi hU (hw (polynomialChart x hi hU))
  obtain ⟨q,hq⟩ := polynomial_form x⁻¹ hj hV (hw (polynomialChart x⁻¹ hj hV))
  by_cases hd : D F K x = 0
  · simp [hp,hd]
  rw [Derivation.leibniz_inv, smul_smul] at hq
  have hz : (aeval x p - aeval x⁻¹ q * -(x⁻¹^2)) • D F K x = 0 := by
    rw [sub_smul, ← hp, ← hq, sub_self]
  have eqn := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hd)
  by_contra hw0
  have hq0 : aeval (RatFunc.X⁻¹ : RatFunc F) q ≠ 0 := by
    intro h
    have hn : aeval x⁻¹ q = 0 := by
      rw [show x⁻¹ = e (RatFunc.X⁻¹) by simp [x], aeval_algHom_apply, h, map_zero]
    exact hw0 (by simp [hq, hn])
  let y : RatFunc F := RatFunc.X⁻¹
  have hy : y ≠ 0 := inv_ne_zero RatFunc.X_ne_zero
  have ht : (algebraMap F[X] (RatFunc F) p) = (aeval y q) * -(y^2) := by
    apply e.injective
    have hp' : aeval x p = e (algebraMap F[X] (RatFunc F) p) := by
      rw [show x = e RatFunc.X from rfl, aeval_algHom_apply]
      have hr : (aeval RatFunc.X : F[X] →ₐ[F] RatFunc F) =
          IsScalarTower.toAlgHom F F[X] (RatFunc F) := by
        apply Polynomial.algHom_ext
        simp [RatFunc.algebraMap_X]
      rw [hr]
      rfl
    simpa [hp', y, map_inv₀, ← aeval_algHom_apply, x] using eqn
  have deg := congrArg RatFunc.intDegree ht
  rw [RatFunc.intDegree_polynomial, RatFunc.intDegree_mul hq0 (neg_ne_zero.mpr (pow_ne_zero _ hy)),
    RatFunc.intDegree_neg, pow_two, RatFunc.intDegree_mul hy hy] at deg
  have hh := inv_polynomial_degree q
  change (aeval y q).intDegree ≤ 0 at hh
  have dd : y.intDegree = -1 := inv_X_degree
  dsimp [y] at hh dd deg
  omega

/-- The geometric genus is zero for every coefficient-preserving rational
function field presentation, since its vector space of regular forms is zero. -/
theorem rational_genus_zero (e : RatFunc F ≃ₐ[F] K) : genus F K = 0 := by
  rw [genus, regularForms_eq_bot e, finrank_bot]

theorem rational_finiteDimensional (e : RatFunc F ≃ₐ[F] K) :
    FiniteDimensional F (regularForms F K) := by
  rw [regularForms_eq_bot e]
  infer_instance

theorem rational_genus_zero_of_ringEquiv (e : RatFunc F ≃+* K)
    (hc : ∀ a : F, e (RatFunc.C a) = algebraMap F K a) : genus F K = 0 :=
  rational_genus_zero ({ e with commutes' := hc } : RatFunc F ≃ₐ[F] K)

end BlockingCurves.CubicRationalGenus
