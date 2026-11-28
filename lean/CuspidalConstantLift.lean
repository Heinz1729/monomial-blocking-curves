import CuspidalGenericAction

/-! Lift the q-power map of the relative algebraic constants while fixing the
intercept parameter. This constructs an arithmetic automorphism in the
original splitting field over the finite field of constants. -/
namespace BlockingCurves.CuspidalGeneral

open Polynomial
noncomputable section

private def fractionMap {K L : Type*} [Field K] [Field L] (φ : K[X] →+* L)
    (inj : Function.Injective φ) : RatFunc K →+* L :=
  RatFunc.liftRingHom φ (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ inj)

private theorem fractionMap_C {K L : Type*} [Field K] [Field L] (φ : K[X] →+* L)
    (inj : Function.Injective φ) (c : K) : fractionMap φ inj (RatFunc.C c) = φ (C c) := by
  simp [fractionMap,RatFunc.liftRingHom_apply]

private theorem fractionMap_X {K L : Type*} [Field K] [Field L] (φ : K[X] →+* L)
    (inj : Function.Injective φ) : fractionMap φ inj RatFunc.X = φ X := by
  simp [fractionMap,RatFunc.liftRingHom_apply]

private theorem fraction_ext {K L : Type*} [Field K] [Field L] {f g : RatFunc K →+* L}
    (hc : ∀ c : K, f (RatFunc.C c) = g (RatFunc.C c)) (hx : f RatFunc.X = g RatFunc.X) :
    f = g := by
  let h := algebraMap K[X] (RatFunc K)
  have pol : f.comp h = g.comp h := Polynomial.ringHom_ext
    (fun c => by simpa [h] using hc c) (by simpa [h] using hx)
  apply RingHom.ext
  intro r
  apply RatFunc.induction_on r
  intro u v _
  rw [map_div₀,map_div₀]
  exact congrArg₂ (· / ·) (RingHom.congr_fun pol u) (RingHom.congr_fun pol v)

private theorem rational_parameter_transcendental (F E : Type*) [Field F] [Field E]
    [Algebra F E] [Algebra (RatFunc F) E] [IsScalarTower F (RatFunc F) E] :
    Transcendental F (algebraMap (RatFunc F) E RatFunc.X) := by
  let x := algebraMap (RatFunc F) E RatFunc.X
  have eqn : aeval x = (IsScalarTower.toAlgHom F (RatFunc F) E).comp
      (IsScalarTower.toAlgHom F F[X] (RatFunc F)) := by
    apply Polynomial.algHom_ext
    simp [x]
  intro h
  apply isAlgebraic_iff_not_injective.mp h
  change Function.Injective (aeval x)
  rw [eqn]
  exact (algebraMap (RatFunc F) E).injective.comp (IsFractionRing.injective F[X] (RatFunc F))

private theorem normal_lift_of_embeddings {A B E : Type*} [Field A] [Field B] [Field E]
    [Algebra A E] [Normal A E] (r : A →+* B) (j j' : B →+* E)
    (base : j.comp r = algebraMap A E) (base' : j'.comp r = algebraMap A E) :
    ∃ σ : E ≃ₐ[A] E, ∀ y : B, σ (j y) = j' y := by
  letI : Algebra A B := r.toAlgebra
  letI : Algebra B E := j.toAlgebra
  letI : IsScalarTower A B E :=
    IsScalarTower.of_algebraMap_eq (S := B) (fun b => (RingHom.congr_fun base b).symm)
  let φ : B →ₐ[A] E := { toRingHom := j', commutes' := RingHom.congr_fun base' }
  let σ := φ.liftNormal E
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective A E E), φ.liftNormal_commutes E⟩

/-- In a normal extension of the rational function field, a single automorphism
acts by q-power on every element algebraic over the finite constant field. -/
theorem exists_constant_frobenius (F E : Type*) [Field F] [Fintype F] [Field E]
    [Algebra (RatFunc F) E] [Algebra F E] [IsScalarTower F (RatFunc F) E]
    [Normal (RatFunc F) E] :
    ∃ σ : E ≃ₐ[RatFunc F] E, ∀ x : E, IsIntegral F x → σ x = x ^ Fintype.card F := by
  classical
  let K : IntermediateField F E := (integralClosure F E).toIntermediateField fun c hc =>
    @Subalgebra.inv_mem_of_algebraic F E _ _ _ (integralClosure F E) ⟨c,hc⟩
      (show IsIntegral F c from hc).isAlgebraic
  letI : Algebra.IsIntegral F K := ⟨fun c =>
    IntermediateField.isIntegral_iff.mpr (show IsIntegral F c.val from c.property)⟩
  let x := algebraMap (RatFunc F) E RatFunc.X
  have xt : Transcendental K x := fun h =>
    rational_parameter_transcendental F E (isIntegral_trans (R := F) x h.isIntegral).isAlgebraic
  let P := (aeval x : K[X] →ₐ[K] E).toRingHom
  have Pinj : Function.Injective P := by
    by_contra h
    exact xt (isAlgebraic_iff_not_injective.mpr h)
  obtain ⟨n,hp,hn⟩ := FiniteField.card F (ringChar F)
  letI : CharP K (ringChar F) := charP_of_injective_algebraMap' F K _
  letI : ExpChar K (ringChar F) := ExpChar.prime hp
  let fr := iterateFrobenius K (ringChar F) n
  have hfr (c : K) : fr c = c ^ Fintype.card F := by
    change c ^ (ringChar F)^(n : ℕ) = _
    rw [←hn]
  let coeff := Polynomial.mapRingHom (algebraMap F K)
  let qmap := Polynomial.mapRingHom fr
  let inc := (algebraMap K[X] (RatFunc K)).comp coeff
  let r := fractionMap inc ((IsFractionRing.injective K[X] (RatFunc K)).comp
    (Polynomial.map_injective (algebraMap F K) (algebraMap F K).injective))
  let j := fractionMap P Pinj
  let j' := fractionMap (P.comp qmap) (Pinj.comp (Polynomial.map_injective fr fr.injective))
  have idC (c : K) : j (RatFunc.C c) = (c:E) := by rw [fractionMap_C]; exact aeval_C _ _
  have frC (c : K) : j' (RatFunc.C c) = (c:E)^Fintype.card F := by
    rw [fractionMap_C]
    change aeval x ((C c).map fr) = _
    rw [Polynomial.map_C,aeval_C,hfr,map_pow]
    rfl
  have rC (c : F) : r (RatFunc.C c) = RatFunc.C (algebraMap F K c) := by
    rw [fractionMap_C]
    simp [inc,coeff]
  have rX : r RatFunc.X = RatFunc.X := by rw [fractionMap_X]; simp [inc,coeff]
  have base : j.comp r = algebraMap (RatFunc F) E := by
    apply fraction_ext
    · intro c
      rw [RingHom.comp_apply,rC,idC]
      exact (IsScalarTower.algebraMap_apply F (RatFunc F) E c).trans rfl
    · rw [RingHom.comp_apply,rX,fractionMap_X]
      exact aeval_X _
  have base' : j'.comp r = algebraMap (RatFunc F) E := by
    apply fraction_ext
    · intro c
      rw [RingHom.comp_apply,rC,frC]
      change (algebraMap F E c) ^ Fintype.card F = _
      rw [←map_pow,FiniteField.pow_card]
      exact IsScalarTower.algebraMap_apply F (RatFunc F) E c
    · rw [RingHom.comp_apply,rX,fractionMap_X]
      change aeval x (((X:K[X])).map fr) = _
      rw [Polynomial.map_X,aeval_X]
  obtain ⟨σ,hσ⟩ := normal_lift_of_embeddings r j j' base base'
  refine ⟨σ,?_⟩
  intro z hz
  let c : K := ⟨z,hz⟩
  simpa only [idC,frC] using hσ (RatFunc.C c)

/-- The arithmetic cusp compositum has a lift of constant-field Frobenius.
Its algebra over F uses the original inclusion F → F(b). -/
theorem cuspCompositum_constant_frobenius {F : Type*} [Field F] [Fintype F]
    (d : ℕ) (a : F) (S : Finset F) :
    ∃ σ : cuspCompositum d a S ≃ₐ[RatFunc F] cuspCompositum d a S,
      ∀ x : cuspCompositum d a S, IsIntegral F x → σ x = x ^ Fintype.card F :=
  exists_constant_frobenius F (cuspCompositum d a S)

private theorem semilinear_embedding {B : Type*} [Field B] (e : B ≃+* B) (P : B[X])
    (h : P.map e.toRingHom = P) : ∃ f : P.SplittingField →+* P.SplittingField,
      ∀ z : B, f (algebraMap B _ z) = algebraMap B _ (e z) := by
  let ι := algebraMap B P.SplittingField
  have split : P.Splits (ι.comp e.toRingHom) := (splits_map_iff _ _).mp
    (by rw [h]; exact SplittingField.splits P)
  let f := @SplittingField.lift B P.SplittingField _ _ P (ι.comp e.toRingHom).toAlgebra split
  exact ⟨@AlgHom.toRingHom B _ _ _ _ _ _ (ι.comp e.toRingHom).toAlgebra f,
    @AlgHom.commutes B _ _ _ _ _ _ (ι.comp e.toRingHom).toAlgebra f⟩

/-- A coefficient automorphism preserving a polynomial lifts semilinearly to
its splitting field. No separability or restriction on the constants is needed. -/
theorem exists_semilinear_splitting_lift {B : Type*} [Field B] (e : B ≃+* B) (P : B[X])
    (h : P.map e.toRingHom = P) : ∃ σ : P.SplittingField ≃+* P.SplittingField,
      ∀ z : B, σ (algebraMap B _ z) = algebraMap B _ (e z) := by
  have hinv : P.map e.symm.toRingHom = P := by
    conv_lhs => arg 2; rw [←h]
    rw [map_map]
    simp
  obtain ⟨f,hf⟩ := semilinear_embedding e P h
  obtain ⟨g,hg⟩ := semilinear_embedding e.symm P hinv
  let H : P.SplittingField →ₐ[B] P.SplittingField :=
    { toRingHom := f.comp g
      commutes' := fun z => by
        change f (g (algebraMap B _ z)) = _
        rw [hg,hf,e.apply_symm_apply] }
  have surj : Function.Surjective (f ∘ g) := (H.normal_bijective B _ _).2
  exact ⟨RingEquiv.ofBijective f ⟨f.injective,surj.of_comp⟩,hf⟩

end
end BlockingCurves.CuspidalGeneral
