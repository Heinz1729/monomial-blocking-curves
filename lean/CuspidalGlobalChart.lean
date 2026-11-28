import CuspidalRootInertia
import CuspidalLiftedSheets
import CubicRepairBranch
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The embedding of the global intercept field in the completion at a
zero fibre, and restriction of local automorphisms to the global compositum. -/
namespace BlockingCurves.CuspidalLocal
open Polynomial CuspidalGeneral
noncomputable section

variable {K : Type*} [Field K]

private def chartPolynomial (n : ℕ) (a α : K) : K[X] :=
  X*(X+C a)^n-C α

private theorem chartPolynomial_degree (n : ℕ) (a α : K) :
    (chartPolynomial n a α).natDegree = n+1 := by
  rw [chartPolynomial,natDegree_sub_C,natDegree_mul X_ne_zero (pow_ne_zero _ (monic_X_add_C a).ne_zero),
    natDegree_X,natDegree_pow,natDegree_X_add_C]
  omega

/-- In the coordinate of the simple sheet, the original intercept remains
transcendental, even if the characteristic divides its polynomial degree. -/
theorem chart_transcendental (n : ℕ) (a α : K) :
    Transcendental K (aeval (CubicRepairBranch.uniformizer K) (chartPolynomial n a α)) := by
  rintro ⟨P,hP,root⟩
  let f := chartPolynomial n a α
  have comp0 : P.comp f = 0 := by
    by_contra h
    exact CubicRepairBranch.uniformizer_transcendental K
      ⟨P.comp f,h,by rwa [aeval_comp]⟩
  obtain h | ⟨_,h⟩ := comp_eq_zero_iff.mp comp0
  · exact hP h
  · have deg := congrArg natDegree h
    rw [natDegree_C] at deg
    change (chartPolynomial n a α).natDegree = 0 at deg
    rw [chartPolynomial_degree] at deg
    omega

/-- The actual embedding of the rational intercept field at b=-α. -/
def chartMap (n : ℕ) (a α : K) : RatFunc K →ₐ[K] LaurentSeries K := by
  let t := aeval (CubicRepairBranch.uniformizer K) (chartPolynomial n a α)
  have inj : Function.Injective (aeval t : K[X] →ₐ[K] LaurentSeries K) := by
    by_contra h
    exact chart_transcendental n a α (isAlgebraic_iff_not_injective.mpr h)
  exact RatFunc.liftAlgHom (aeval t) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ inj)

@[simp] theorem chartMap_X (n : ℕ) (a α : K) :
    chartMap n a α RatFunc.X = CubicRepairBranch.uniformizer K *
      (algebraMap K (LaurentSeries K) a+CubicRepairBranch.uniformizer K)^n -
      algebraMap K (LaurentSeries K) α := by
  simp [chartMap,chartPolynomial,RatFunc.liftAlgHom_apply,add_comm]

@[simp] theorem chartMap_C (n : ℕ) (a α c : K) :
    chartMap n a α (RatFunc.C c) = algebraMap K (LaurentSeries K) c :=
  (chartMap n a α).commutes c

abbrev ChartClosure (K : Type*) [Field K] := AlgebraicClosure (LaurentSeries K)

def chartBase (n : ℕ) (a α : K) : RatFunc K →+* ChartClosure K :=
  (algebraMap (LaurentSeries K) (ChartClosure K)).comp (chartMap n a α).toRingHom

/-- Embed the splitting field of the entire product into an algebraic closure
of the Laurent field, over the displayed (usually nongeneric) local chart. -/
def globalEmbedding (n : ℕ) (a α : K) (S : Finset K) :
    cuspCompositum (n+1) a S →+* ChartClosure K := by
  letI : Algebra (RatFunc K) (ChartClosure K) := (chartBase n a α).toAlgebra
  let P := ∏ v ∈ S, cuspCoordinate (n+1) a v
  exact (IsSplittingField.lift P.SplittingField P (IsAlgClosed.splits_codomain P)).toRingHom

theorem globalEmbedding_base (n : ℕ) (a α : K) (S : Finset K) (b : RatFunc K) :
    globalEmbedding n a α S (algebraMap (RatFunc K) _ b) = chartBase n a α b := by
  letI : Algebra (RatFunc K) (ChartClosure K) := (chartBase n a α).toAlgebra
  exact (IsSplittingField.lift _ _ (IsAlgClosed.splits_codomain _)).commutes b

/-- Restriction of a local automorphism to the actual global splitting
field, with its action on every element identified through one fixed
embedding. No normality of the Laurent extension of the intercept is needed. -/
theorem descend_local_action (n : ℕ) (a α : K) (S : Finset K)
    (σ : ChartClosure K ≃ₐ[LaurentSeries K] ChartClosure K) :
    ∃ g : cuspCompositum (n+1) a S ≃ₐ[RatFunc K] cuspCompositum (n+1) a S,
      ∀ x, globalEmbedding n a α S (g x) = σ (globalEmbedding n a α S x) := by
  let G := cuspCompositum (n+1) a S
  let Ω := ChartClosure K
  letI : Algebra (RatFunc K) Ω := (chartBase n a α).toAlgebra
  letI : Algebra G Ω := (globalEmbedding n a α S).toAlgebra
  letI : SMul (RatFunc K) G := Algebra.toSMul
  letI : SMul (RatFunc K) Ω := Algebra.toSMul
  letI : IsScalarTower (RatFunc K) G Ω := IsScalarTower.of_algebraMap_eq
    fun b => (globalEmbedding_base n a α S b).symm
  let τ : Ω ≃ₐ[RatFunc K] Ω := AlgEquiv.ofRingEquiv (f:=σ.toRingEquiv)
    (fun b => σ.commutes (chartMap n a α b))
  exact ⟨τ.restrictNormal G,τ.restrictNormal_commutes G⟩

/-- The intercept in power series on the simple branch at -α, with the
additional translate v. Its reduction is v-α. -/
def chartIntercept (n : ℕ) (a α v : K) : PowerSeries K :=
  PowerSeries.X*(PowerSeries.C K a + PowerSeries.X)^n + PowerSeries.C K (v-α)

@[simp] theorem chartIntercept_constant (n : ℕ) (a α v : K) :
    PowerSeries.constantCoeff K (chartIntercept n a α v) = v-α := by simp [chartIntercept]

theorem chart_coordinate (n : ℕ) (a α v : K) :
    (cuspCoordinate (n+1) a v).map (chartMap n a α).toRingHom =
      (integralFibre (n+1) (PowerSeries.C K a) (chartIntercept n a α v)).map
        (algebraMap (PowerSeries K) (LaurentSeries K)) := by
  let φ := algebraMap (PowerSeries K) (LaurentSeries K)
  have hc (r : K) : φ (PowerSeries.C K r) = algebraMap K (LaurentSeries K) r := by
    rw [HahnSeries.algebraMap_apply' ℤ]
    rfl
  have hu : φ PowerSeries.X = CubicRepairBranch.uniformizer K := PowerSeries.coe_X
  have intercept : (chartMap n a α).toRingHom (RatFunc.X+RatFunc.C v) =
      φ (chartIntercept n a α v) := by
    change chartMap n a α (RatFunc.X+RatFunc.C v) = _
    simp only [map_add,chartMap_C,chartMap_X,chartIntercept,map_mul,map_pow,hc,hu,map_sub]
    ring
  simp only [cuspCoordinate,lineFibre,integralFibre,Polynomial.map_sub,Polynomial.map_add,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  rw [intercept,show (chartMap n a α).toRingHom (RatFunc.C a) = φ (PowerSeries.C K a) from
    (chartMap_C n a α a).trans (hc a).symm]

/-- Embedded evaluation of the global polynomial agrees with its Laurent
expression on the same embedded root. -/
theorem chart_root_test (n : ℕ) (a α v : K) (S : Finset K)
    {x : cuspCompositum (n+1) a S} (hx : x ∈ (cuspCoordinate (n+1) a v).rootSet _) :
    aeval (globalEmbedding n a α S x)
      ((cuspCoordinate (n+1) a v).map (chartMap n a α).toRingHom) = 0 := by
  let P := cuspCoordinate (n+1) a v
  let ι := globalEmbedding n a α S
  have root := congrArg ι (mem_rootSet.mp hx).2
  rw [aeval_def,hom_eval₂,map_zero] at root
  have eq : ι.comp (algebraMap (RatFunc K) _) = chartBase n a α :=
    RingHom.ext (globalEmbedding_base n a α S)
  simpa only [P,ι,aeval_def,eval₂_map,eq,chartBase] using root

private theorem coord_ne_zero (n : ℕ) (a v : K) : cuspCoordinate (n+1) a v ≠ 0 := by
  cases n with
  | zero =>
    change X^1-(C (RatFunc.C a)*X^0 + C (RatFunc.X+RatFunc.C v)) ≠ 0
    rw [pow_one,pow_zero,mul_one,← Polynomial.C_add]
    exact X_sub_C_ne_zero _
  | succ n => exact (integralFibre_monic (d:=n+1+1) (by omega)
      (RatFunc.C a) (RatFunc.X+RatFunc.C v)).ne_zero

/-- Every local root comes from a root in the *same fixed embedding*
of the global product splitting field. -/
theorem global_root_of_local_root (n : ℕ) (a α v : K) (S : Finset K) (hv : v∈S)
    (z : ChartClosure K)
    (hz : aeval z ((cuspCoordinate (n+1) a v).map (chartMap n a α).toRingHom) = 0) :
    ∃ x ∈ (cuspCoordinate (n+1) a v).rootSet (cuspCompositum (n+1) a S),
      globalEmbedding n a α S x=z := by
  let P := cuspCoordinate (n+1) a v
  let f := ∏ w ∈ S, cuspCoordinate (n+1) a w
  let G := cuspCompositum (n+1) a S
  letI : Algebra (RatFunc K) (ChartClosure K) := (chartBase n a α).toAlgebra
  let i : G →ₐ[RatFunc K] ChartClosure K :=
    { globalEmbedding n a α S with commutes' := globalEmbedding_base n a α S }
  have nz : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => coord_ne_zero n a w
  have split : P.Splits (algebraMap (RatFunc K) G) :=
    splits_of_splits_of_dvd _ nz (IsSplittingField.splits f.SplittingField f)
      (Finset.dvd_prod_of_mem _ hv)
  have mem : z ∈ P.rootSet (ChartClosure K) := by
    apply mem_rootSet.mpr ⟨coord_ne_zero n a v,?_⟩
    simpa only [aeval_def,eval₂_map] using hz
  rw [← image_rootSet split i] at mem
  exact mem

/-- Each separated coordinate already splits over the Laurent base.
Consequently its global roots are fixed by every local automorphism. -/
private theorem fixed_of_split {L E : Type*} [Field L] [Field E] [Algebra L E] (Q : L[X])
    (split : Q.Splits (RingHom.id L)) (σ : E ≃ₐ[L] E) {z : E} (mem : z ∈ Q.rootSet E) :
    σ z = z := by
  rw [← image_rootSet (show Q.Splits (algebraMap L L) from split) (Algebra.ofId L E)] at mem
  obtain ⟨r,_,hr⟩ := mem
  rw [← hr]
  exact σ.commutes _

theorem fixes_other_chart_root [IsAlgClosed K] {n : ℕ} (hd : 3≤n+1) {a α v : K}
    (ha : a≠0)
    (apart : Disjoint ({-α,extraCritical (n+1) a-α} : Set K) {-v,extraCritical (n+1) a-v})
    (S : Finset K) (σ : ChartClosure K ≃ₐ[LaurentSeries K] ChartClosure K)
    {x : cuspCompositum (n+1) a S} (hx : x∈(cuspCoordinate (n+1) a v).rootSet _) :
    σ (globalEmbedding n a α S x) = globalEmbedding n a α S x := by
  let Q := (cuspCoordinate (n+1) a v).map (chartMap n a α).toRingHom
  have zero : v-α ≠ 0 := by
    intro h
    exact Set.disjoint_left.mp apart (Set.mem_insert _ _)
      (by rw [sub_eq_zero.mp h]; exact Set.mem_insert _ _)
  have extra : v-α ≠ extraCritical (n+1) a := by
    intro h
    exact Set.disjoint_left.mp apart (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_singleton_iff.mpr (by linear_combination h)))
  have split : Q.Splits (RingHom.id _) := by
    rw [show Q = _ by exact chart_coordinate n a α v]
    apply separated_local_coordinate_splits hd a ha
    · simpa only [chartIntercept_constant] using zero
    · simpa only [chartIntercept_constant] using extra
  have hQ : Q≠0 := Polynomial.map_ne_zero (coord_ne_zero n a v)
  let z := globalEmbedding n a α S x
  have mem : z∈Q.rootSet (ChartClosure K) := mem_rootSet.mpr ⟨hQ,chart_root_test n a α v S hx⟩
  exact fixed_of_split Q split σ mem

end
end BlockingCurves.CuspidalLocal
