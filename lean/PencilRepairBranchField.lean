import PencilRepairBranch
import CubicRationalGenus

/-! The simultaneous root field as a concrete subextension of Laurent series. -/
namespace BlockingCurves.PencilRepairBranch
open Polynomial IntermediateField FiniteDimensional PencilSampling
noncomputable section
universe u
variable {F : Type u} [Field F]

def parameterMap (F : Type u) [Field F] {d : ℕ} (hd : 0 < d) : RatFunc F →ₐ[F] LaurentSeries F := by
  let a := ((CubicRepairBranch.uniformizer F)^d)⁻¹
  have ht : Transcendental F a := fun h =>
    (CubicRepairBranch.uniformizer_transcendental F).pow hd (IsAlgebraic.inv_iff.mp h)
  have hi : Function.Injective (aeval a : F[X] →ₐ[F] LaurentSeries F) := by
    by_contra h
    exact ht (isAlgebraic_iff_not_injective.mpr h)
  exact RatFunc.liftAlgHom (aeval a) (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hi)

@[simp] theorem parameterMap_X {d : ℕ} (hd : 0 < d) :
    parameterMap F hd RatFunc.X = ((CubicRepairBranch.uniformizer F)^d)⁻¹ := by
  simp [parameterMap,RatFunc.liftAlgHom_apply]

/-- Common root field, with a specified Laurent embedding and its parameter. -/
structure Model (F : Type u) [Field F] (d : ℕ) (R : Finset (Lines F)) where
  K : Type u
  [fieldK : Field K]
  [algebraK : Algebra (RatFunc F) K]
  root : R → K
  equation : ∀ i, (root i)^d = algebraMap (RatFunc F) K (RatFunc.C (coordinates i.val).1)*root i +
    algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C (coordinates i.val).2)
  generated : adjoin (RatFunc F) (Set.range root) = ⊤
  embed : K →+* LaurentSeries F
  onConstants : ∀ a : F, embed (algebraMap (RatFunc F) K (RatFunc.C a)) = algebraMap F (LaurentSeries F) a
  onParameter : embed (algebraMap (RatFunc F) K RatFunc.X) = ((CubicRepairBranch.uniformizer F)^d)⁻¹

attribute [instance] Model.fieldK Model.algebraK

theorem model_exists {d : ℕ} (hd : 2 ≤ d) (hp : (d:F) ≠ 0) (R : Finset (Lines F)) :
    Nonempty (Model F d R) := by
  let φ := HahnSeries.ofPowerSeries ℤ F
  have hu : φ PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).mpr PowerSeries.X_ne_zero
  obtain ⟨y,hy⟩ := simultaneous_roots hd hp
    (fun i : R => (coordinates i.val).1) (fun i : R => (coordinates i.val).2) φ hu
  let x := fun i : R => φ (y i)/φ PowerSeries.X
  let β := parameterMap F (by omega : 0 < d)
  letI : Algebra (RatFunc F) (LaurentSeries F) := β.toRingHom.toAlgebra
  let K := adjoin (RatFunc F) (Set.range x)
  let root : R → K := fun i => ⟨x i,subset_adjoin _ _ ⟨i,rfl⟩⟩
  have eqn (i : R) : (root i)^d =
      algebraMap (RatFunc F) K (RatFunc.C (coordinates i.val).1) * root i +
      algebraMap (RatFunc F) K (RatFunc.X + RatFunc.C (coordinates i.val).2) := by
    apply Subtype.ext
    change (x i)^d = β (RatFunc.C _) * x i + β (RatFunc.X + RatFunc.C _)
    have he := (hy i).2
    change (x i)^d - φ (PowerSeries.C F _) * x i - φ (PowerSeries.C F _) =
      ((φ PowerSeries.X)^d)⁻¹ at he
    have hC (a : F) : φ (PowerSeries.C F a) = β (RatFunc.C a) := by
      rw [show β (RatFunc.C a) = algebraMap F (LaurentSeries F) a from β.commutes a]
      rw [HahnSeries.algebraMap_apply' ℤ, ← PowerSeries.C_eq_algebraMap]
    rw [hC,hC] at he
    have hX : φ PowerSeries.X = CubicRepairBranch.uniformizer F := HahnSeries.ofPowerSeries_X
    rw [hX, ← parameterMap_X (by omega : 0 < d)] at he
    rw [map_add]
    linear_combination he
  have gen : adjoin (RatFunc F) (Set.range root) = ⊤ := by
    apply K.lift_injective
    rw [lift_adjoin, lift_top, ← Set.range_comp]
    rfl
  exact ⟨⟨K,root,eqn,gen,K.val.toRingHom,β.commutes,parameterMap_X (by omega)⟩⟩

variable {d : ℕ} {R : Finset (Lines F)}

/-- The restriction of the Laurent valuation gives a rational place over infinity. -/
theorem rational_pole (hd : 2 ≤ d) (D : Model F d R) :
    ∃ v : CubicRepairPlaces.RationalPlace F D.K, algebraMap (RatFunc F) D.K RatFunc.X ∉ v.ring :=
  CubicRepairBranch.rational_pole_of_embedding (by omega : 0 < d) D.embed D.onConstants D.onParameter

/-- Algebraic constants of the actual branch are exactly the coefficient field. -/
theorem full_constants [Fintype F] (D : Model F d R) :
    letI : Algebra F D.K := ((algebraMap (RatFunc F) D.K).comp RatFunc.C).toAlgebra
    ∀ x : D.K, IsAlgebraic F x → ∃ a : F, x = algebraMap F D.K a := by
  letI : Algebra F D.K := ((algebraMap (RatFunc F) D.K).comp RatFunc.C).toAlgebra
  let e : D.K →ₐ[F] LaurentSeries F := {D.embed with commutes' := D.onConstants}
  intro x hx
  refine ⟨(D.embed x).coeff 0,D.embed.injective ?_⟩
  rw [show algebraMap F D.K _ = algebraMap (RatFunc F) D.K (RatFunc.C _) from rfl, D.onConstants]
  exact CubicRepairBranch.algebraic_constant F _ (hx.algHom e)

private theorem one_degree {B K : Type*} [Field B] [Field K] [Algebra B K] (hd : 2 ≤ d)
    (x : K) (m c : B) (he : x^d = algebraMap B K m*x + algebraMap B K c) :
    FiniteDimensional B (adjoin B {x}) ∧ finrank B (adjoin B {x}) ≤ d := by
  obtain ⟨k,rfl⟩ : ∃ k, d = k+2 := ⟨d-2,by omega⟩
  let f : B[X] := C m * X + C c
  have hf : f.natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · exact natDegree_mul_le.trans (by simp)
    · simp
  let P : B[X] := X^(k+2)-f
  have hm : P.Monic := monic_X_pow_sub (degree_le_of_natDegree_le (hf.trans (by omega)))
  have hz : aeval x P = 0 := by simp [P,f,he]
  have hi : IsIntegral B x := ⟨P,hm,hz⟩
  refine ⟨adjoin.finiteDimensional hi,?_⟩
  rw [adjoin.finrank hi]
  apply (natDegree_le_natDegree (minpoly.min B x hm hz)).trans
  exact (natDegree_sub_le _ _).trans (max_le (by simp) (by omega))

/-- The field obtained by adjoining a specified root for each line is finite of
degree at most d to the number of lines. This also bounds both degrees in a compositum. -/
theorem generated_degree {B K I : Type*} [Field B] [Field K] [Algebra B K]
    (hd : 2 ≤ d) (S : Finset I) (x : I → K) (m c : I → B)
    (hx : ∀ i ∈ S, (x i)^d = algebraMap B K (m i)*x i + algebraMap B K (c i)) :
    FiniteDimensional B (adjoin B (x '' (S:Set I))) ∧
      finrank B (adjoin B (x '' (S:Set I))) ≤ d^S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    let Q (L : IntermediateField B K) := FiniteDimensional B L ∧ finrank B L ≤ d^(∅ : Finset I).card
    change Q _
    rw [Finset.coe_empty, Set.image_empty, adjoin_empty]
    exact ⟨inferInstance, by simp only [IntermediateField.finrank_bot, Finset.card_empty, pow_zero, le_refl]⟩
  | @insert i S hi ih =>
    obtain ⟨hfinite,hdegree⟩ := ih (fun j hj => hx j (Finset.mem_insert_of_mem hj))
    let A := adjoin B (x '' (S:Set I))
    let D := adjoin A {x i}
    letI : FiniteDimensional B A := hfinite
    have heq : (x i)^d = algebraMap A K (algebraMap B A (m i))*x i +
        algebraMap A K (algebraMap B A (c i)) := by
      simpa only [← IsScalarTower.algebraMap_apply B A K] using hx i (Finset.mem_insert_self i S)
    obtain ⟨hnew,hle⟩ := one_degree hd (x i) (algebraMap B A (m i)) (algebraMap B A (c i)) heq
    letI : FiniteDimensional A D := hnew
    have hfield : D.restrictScalars B = adjoin B (x '' (↑(insert i S) : Set I)) := by
      rw [Finset.coe_insert,Set.image_insert_eq,← Set.singleton_union, Set.union_comm]
      exact adjoin_adjoin_left _ _ _
    let Q (L : IntermediateField B K) := FiniteDimensional B L ∧ finrank B L ≤ d^(insert i S).card
    change Q _
    rw [← hfield]
    refine ⟨FiniteDimensional.trans B A D,?_⟩
    change finrank B D ≤ _
    rw [← finrank_mul_finrank B A D, Finset.card_insert_of_not_mem hi,pow_succ]
    exact Nat.mul_le_mul hdegree hle

theorem model_degree (hd : 2 ≤ d) (D : Model F d R) : FiniteDimensional (RatFunc F) D.K ∧
    finrank (RatFunc F) D.K ≤ d^R.card := by
  have h := generated_degree hd (Finset.univ : Finset R) D.root
    (fun i => RatFunc.C (coordinates i.val).1) (fun i => RatFunc.X+RatFunc.C (coordinates i.val).2)
    (fun i _ => D.equation i)
  let Q (L : IntermediateField (RatFunc F) D.K) := FiniteDimensional (RatFunc F) L ∧
    finrank (RatFunc F) L ≤ d^(Finset.univ : Finset R).card
  change Q _ at h
  rw [Finset.coe_univ,Set.image_univ,D.generated] at h
  letI : FiniteDimensional (RatFunc F) (⊤ : IntermediateField (RatFunc F) D.K) := h.1
  refine ⟨FiniteDimensional.of_injective (IntermediateField.topEquiv.toLinearEquiv.symm : D.K ≃ₗ[RatFunc F] _)
    (IntermediateField.topEquiv (F := RatFunc F) (E := D.K)).symm.injective, ?_⟩
  simpa only [finrank_top', Finset.card_univ, Fintype.card_coe] using h.2

end
end BlockingCurves.PencilRepairBranch
