import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Adjoin
import Mathlib.FieldTheory.Finite.Basic
import CubicRepairPlaces
import CubicRepairChart

/-! The common branch at infinity is modeled inside Laurent series over the
ground field. Its rational parameter is the inverse cube of the series variable. -/
namespace BlockingCurves.CubicRepairBranch
open Polynomial IntermediateField
noncomputable section
variable (F : Type*) [Field F]

def uniformizer : LaurentSeries F := HahnSeries.single 1 1

private theorem constant_eq (a : F) :
    algebraMap F (LaurentSeries F) a = HahnSeries.single 0 a := by
  rw [HahnSeries.algebraMap_apply' ℤ, ← PowerSeries.C_eq_algebraMap,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

theorem uniformizer_transcendental : Transcendental F (uniformizer F) := by
  let e : F[X] →ₐ[F] LaurentSeries F :=
    { algebraMap F[X] (LaurentSeries F) with
      commutes' := fun a => by
        change algebraMap F[X] (LaurentSeries F) (C a) = _
        simp
        exact (constant_eq F a).symm }
  have he : aeval (uniformizer F) = e := by
    apply Polynomial.algHom_ext
    change aeval (uniformizer F) X = algebraMap F[X] (LaurentSeries F) X
    simp [uniformizer]
  intro halg
  apply isAlgebraic_iff_not_injective.mp halg
  rw [he]
  exact Polynomial.algebraMap_hahnSeries_injective ℤ

def parameterMap : RatFunc F →ₐ[F] LaurentSeries F := by
  let a := ((uniformizer F)^3)⁻¹
  have htrans : Transcendental F a := fun h =>
    ((uniformizer_transcendental F).pow (by decide : 0 < 3)) (IsAlgebraic.inv_iff.mp h)
  have hinj : Function.Injective (aeval a : F[X] →ₐ[F] LaurentSeries F) := by
    by_contra h
    exact htrans (isAlgebraic_iff_not_injective.mpr h)
  exact RatFunc.liftAlgHom (aeval a) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hinj)

@[simp] theorem parameterMap_X : parameterMap F RatFunc.X = ((uniformizer F)^3)⁻¹ := by
  simp [parameterMap, RatFunc.liftAlgHom_apply]

@[simp] theorem parameterMap_C (a : F) :
    parameterMap F (RatFunc.C a) = algebraMap F (LaurentSeries F) a :=
  (parameterMap F).commutes a

/-- Any element algebraic over the finite coefficient field has order zero. -/
theorem algebraic_order [Fintype F] (x : LaurentSeries F) (hx : IsAlgebraic F x) :
    x.order = 0 := by
  classical
  by_cases hz : x = 0
  · simp [hz]
  let D := adjoin F {x}
  letI : FiniteDimensional F D := adjoin.finiteDimensional hx.isIntegral
  letI : Fintype D := Module.fintypeOfFintype (FiniteDimensional.finBasis F D)
  let y : D := ⟨x,mem_adjoin_simple_self F x⟩
  have hy : y ≠ 0 := fun h => hz (congrArg Subtype.val h)
  have he := FiniteField.pow_card_sub_one_eq_one y hy
  have he' : x^(Fintype.card D-1) = 1 := congrArg (fun z : D => (z : LaurentSeries F)) he
  have hdr : (Fintype.card D-1 : ℕ) ≠ 0 := by have h := Fintype.one_lt_card (α := D); omega
  have h := congrArg HahnSeries.order he'
  rw [HahnSeries.order_pow, HahnSeries.order_one, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hdr)

/-- The coefficient field is relatively algebraically closed in its Laurent
series field. This also applies to every embedded common-root subfield. -/
theorem algebraic_constant [Fintype F] (x : LaurentSeries F) (hx : IsAlgebraic F x) :
    x = algebraMap F (LaurentSeries F) (x.coeff 0) := by
  let c := algebraMap F (LaurentSeries F) (x.coeff 0)
  have hd : IsAlgebraic F (x-c) :=
    (hx.isIntegral.sub (isIntegral_algebraMap : IsIntegral F c)).isAlgebraic
  by_contra h
  have hs : (x-c).coeff (x-c).order ≠ 0 := HahnSeries.coeff_order_ne_zero (sub_ne_zero.mpr h)
  rw [algebraic_order F _ hd] at hs
  apply hs
  simp [c, constant_eq]

open CubicAlteration CubicRepairPlaces
variable {F}

/-- A common branch with its Laurent expansion, preserving the prescribed
parameter and its coefficient field. -/
structure Expansion {R : Finset (Line F)} (D : Branch F R) where
  embed : D.K →+* LaurentSeries F
  onConstant : ∀ a : F, embed (constant D a) = algebraMap F (LaurentSeries F) a
  onParameter : embed (parameter D) = ((uniformizer F)^3)⁻¹

theorem exists_expansion (R : Finset (Line F)) (h3 : (3:F) ≠ 0) :
    ∃ D : Branch F R, Nonempty (Expansion D) := by
  classical
  let φ := HahnSeries.ofPowerSeries ℤ F
  have hu : φ PowerSeries.X ≠ 0 := by
    change HahnSeries.ofPowerSeries ℤ F PowerSeries.X ≠ 0
    exact (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr PowerSeries.X_ne_zero
  obtain ⟨y,hy⟩ := CubicRepairChart.simultaneous_roots_at_inverse_cube
    (fun i : R => (i.val.1:F)) (fun i : R => i.val.2) h3 φ hu
  let x := fun i : R => φ (y i) / φ PowerSeries.X
  let β := parameterMap F
  letI : Algebra (RatFunc F) (LaurentSeries F) := β.toRingHom.toAlgebra
  let K := adjoin (RatFunc F) (Set.range x)
  let root : R → K := fun i => ⟨x i,subset_adjoin _ _ ⟨i,rfl⟩⟩
  have eqn (i : R) : (root i)^3 =
      algebraMap (RatFunc F) K (RatFunc.C (i.val.1:F)) * root i +
      algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C i.val.2) := by
    apply Subtype.ext
    change (x i)^3 = β (RatFunc.C _) * x i + β (RatFunc.X + RatFunc.C _)
    simp only [β, map_add, parameterMap_X, parameterMap_C]
    have he := (hy i).2
    change (x i)^3 - φ (PowerSeries.C F _) * x i - φ (PowerSeries.C F _) =
      (φ PowerSeries.X)⁻¹^3 at he
    have hc (a : F) : φ (PowerSeries.C F a) = algebraMap F (LaurentSeries F) a := by
      simp [φ,constant_eq,HahnSeries.C_apply]
    simp only [hc, inv_pow] at he
    change (x i)^3 - _ * x i - _ = (HahnSeries.ofPowerSeries ℤ F PowerSeries.X ^ 3)⁻¹ at he
    rw [HahnSeries.ofPowerSeries_X] at he
    dsimp [uniformizer]
    linear_combination he
  have gen : adjoin (RatFunc F) (Set.range root) = ⊤ := by
    apply K.lift_injective
    rw [lift_adjoin, lift_top, ← Set.range_comp]
    rfl
  let D : Branch F R := ⟨K,root,eqn,gen⟩
  refine ⟨D,⟨⟨K.val.toRingHom,?_,?_⟩⟩⟩
  · exact parameterMap_C F
  · exact parameterMap_X F

private theorem inverse_order (x : LaurentSeries F) (hx : x ≠ 0) :
    x⁻¹.order = -x.order := by
  have he := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel hx, HahnSeries.order_one] at he
  omega

private theorem powerSeries_range_iff (x : LaurentSeries F) :
    x ∈ (HahnSeries.ofPowerSeries ℤ F).range ↔ 0 ≤ x.order := by
  constructor
  · rintro ⟨y,rfl⟩
    by_contra! h
    let w := HahnSeries.ofPowerSeries ℤ F y
    have hw : w ≠ 0 := fun hz => by
      change w.order < 0 at h
      rw [hz,HahnSeries.order_zero] at h
      exact (lt_irrefl _) h
    apply HahnSeries.coeff_order_ne_zero hw
    change ((y : PowerSeries F) : LaurentSeries F).coeff w.order = 0
    rw [PowerSeries.coeff_coe, if_pos h]
  · intro h
    refine ⟨PowerSeries.X ^ x.order.toNat * x.powerSeriesPart, ?_⟩
    rw [map_mul,map_pow,HahnSeries.ofPowerSeries_X,← RatFunc.single_one_eq_pow,
      Int.toNat_of_nonneg h]
    exact LaurentSeries.single_order_mul_powerSeriesPart x

private def seriesRing (F : Type*) [Field F] : ValuationSubring (LaurentSeries F) :=
  { (HahnSeries.ofPowerSeries ℤ F).range with
    mem_or_inv_mem' := fun x => by
      change x ∈ (HahnSeries.ofPowerSeries ℤ F).range ∨
        x⁻¹ ∈ (HahnSeries.ofPowerSeries ℤ F).range
      rw [powerSeries_range_iff,powerSeries_range_iff]
      by_cases h : 0 ≤ x.order
      · exact Or.inl h
      · right
        have hx : x ≠ 0 := fun he => h (by simp [he])
        rw [inverse_order x hx]; omega }

private theorem coeff_zero (p : PowerSeries F) :
    (HahnSeries.ofPowerSeries ℤ F p).coeff 0 = PowerSeries.constantCoeff F p := by
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using LaurentSeries.coeff_coe_powerSeries p 0

private def seriesResidue : seriesRing F →+* F where
  toFun := fun v => (v : LaurentSeries F).coeff 0
  map_one' := by simp
  map_zero' := by simp
  map_add' := fun a b => by rfl
  map_mul' := fun a b => by
    obtain ⟨p,hp⟩ := a.property
    obtain ⟨q,hq⟩ := b.property
    change ((a : LaurentSeries F)*(b : LaurentSeries F)).coeff 0 =
      (a : LaurentSeries F).coeff 0 * (b : LaurentSeries F).coeff 0
    rw [←hp,←hq,←map_mul,coeff_zero,coeff_zero,coeff_zero,map_mul]

/-- The valuation ring of regular Laurent series gives a rational pole above
infinity for any embedded function field whose parameter is z⁻ᵈ. -/
theorem rational_pole_of_embedding {K : Type*} [Field K] [Algebra (RatFunc F) K]
    {d : ℕ} (hd : 0 < d) (φ : K →+* LaurentSeries F)
    (hC : ∀ a : F, φ (baseConstant F K a) = algebraMap F (LaurentSeries F) a)
    (hT : φ (algebraMap (RatFunc F) K RatFunc.X) = ((uniformizer F)^d)⁻¹) :
    ∃ v : RationalPlace F K, algebraMap (RatFunc F) K RatFunc.X ∉ v.ring := by
  let V := (seriesRing F).comap φ
  have hc (a : F) : baseConstant F K a ∈ V := by
    change φ (baseConstant F K a) ∈ (HahnSeries.ofPowerSeries ℤ F).range
    rw [hC]
    exact ⟨PowerSeries.C F a, by simp [constant_eq,HahnSeries.C_apply]⟩
  let g : V →+* seriesRing F :=
    { toFun := fun x => ⟨φ x.val,x.property⟩
      map_one' := Subtype.ext (map_one _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_mul' := fun x y => Subtype.ext (map_mul _ _ _) }
  let v : RationalPlace F K :=
    { ring := V
      constants := hc
      residue := seriesResidue.comp g
      on_constants := fun a => by
        change (φ (baseConstant F K a)).coeff 0 = a
        rw [hC, constant_eq]; simp }
  refine ⟨v,?_⟩
  change φ (algebraMap (RatFunc F) K RatFunc.X) ∉ (HahnSeries.ofPowerSeries ℤ F).range
  rw [hT, powerSeries_range_iff]
  have hz : uniformizer F ≠ 0 := HahnSeries.single_ne_zero one_ne_zero
  rw [inverse_order _ (pow_ne_zero _ hz), HahnSeries.order_pow]
  simp [uniformizer, HahnSeries.order_single one_ne_zero, hd.ne']

/-- The cubic Laurent expansion has a rational pole above infinity. -/
theorem infinity_place {R : Finset (Line F)} {D : Branch F R} (e : Expansion D) :
    ∃ v : Place D, parameter D ∉ v.ring :=
  rational_pole_of_embedding (by decide : 0 < 3) e.embed e.onConstant e.onParameter

/-- The coefficient field of the branch contains all its algebraic constants. -/
def FullConstants {R : Finset (Line F)} (D : Branch F R) : Prop :=
  letI := (constant D).toAlgebra
  ∀ x : D.K, IsAlgebraic F x → ∃ a : F, x = constant D a

theorem full_constants [Fintype F] {R : Finset (Line F)} {D : Branch F R}
    (e : Expansion D) : FullConstants D := by
  letI := (constant D).toAlgebra
  let k : D.K →ₐ[F] LaurentSeries F := {e.embed with commutes' := e.onConstant}
  intro x hx
  refine ⟨(e.embed x).coeff 0,e.embed.injective ?_⟩
  rw [e.onConstant]
  exact algebraic_constant F _ (hx.algHom k)

/-- A generated branch over the exact constant field with a degree-one place
above infinity, for every list of lines and every characteristic other than 3. -/
theorem exists_rational_branch [Fintype F] (R : Finset (Line F)) (h3 : (3:F) ≠ 0) :
    ∃ D : Branch F R, FullConstants D ∧ ∃ v : Place D, parameter D ∉ v.ring := by
  obtain ⟨D,⟨e⟩⟩ := exists_expansion R h3
  exact ⟨D, full_constants e, infinity_place e⟩

end
end BlockingCurves.CubicRepairBranch
