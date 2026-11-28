import CuspidalGeometricFrobenius
import CuspidalTwistFibre

/-! Specialization at a Frobenius-stable valuation above a regular intercept.
Reduction identifies the two root permutations up to conjugacy. -/
namespace BlockingCurves.CuspidalGeneral
open Polynomial PencilSampling
noncomputable section

variable {F : Type*} [Field F] [Fintype F]

private abbrev geom (d : ℕ) (a : F) (S : Finset F) := GeometricSplitting d a S
private abbrev geomAut (d : ℕ) (a : F) (S : Finset F) :=
  geom d a S ≃ₐ[RatFunc (AlgebraicClosure F)] geom d a S

/-- A geometric valuation above the intercept b, preserved as a ring by
the chosen semilinear element. Its action on the residue roots is derived. -/
structure StableTwistPlace (d : ℕ) (a : F) (S : Finset F) (g : geomAut d a S) (b : F) where
  ring : ValuationSubring (geom d a S)
  over : CuspPlace ring (-(algebraMap F (AlgebraicClosure F) b))
  stable : ∀ x, geometricFrobenius d a S (g x) ∈ ring ↔ x ∈ ring

private def restrictRing {M : Type*} [Field M] (O : ValuationSubring M)
    (τ : M ≃+* M) (stable : ∀ x, τ x ∈ O ↔ x ∈ O) : O ≃+* O where
  toFun x := ⟨τ x,(stable _).mpr x.property⟩
  invFun x := ⟨τ.symm x,(stable _).mp (by rw [τ.apply_symm_apply]; exact x.property)⟩
  left_inv x := Subtype.ext (τ.symm_apply_apply _)
  right_inv x := Subtype.ext (τ.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

private theorem component_constants {d : ℕ} {a : F} {S : Finset F}
    (g : geomAut d a S) (c : AlgebraicClosure F) :
    geometricFrobenius d a S (g (algebraMap _ _ (RatFunc.C c))) =
      algebraMap _ _ (RatFunc.C (c^Fintype.card F)) := by
  rw [g.commutes,geometricFrobenius_extends,coefficientFrobenius_C]

private theorem labelled_root_equation {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F) (α : S) (i : Fin d) :
    let f := algebraMap F (AlgebraicClosure F)
    let ι := algebraMap (RatFunc (AlgebraicClosure F)) (geom d a S)
    let z := (rootLabel hd ha S α i).val
    z^d = ι (RatFunc.C (f a))*z^(d-1) + (ι RatFunc.X + ι (RatFunc.C (f α.val))) := by
  have h := (mem_rootSet.mp (rootLabel hd ha S α i).property).2
  simpa only [cuspCoordinate,lineFibre,map_sub,map_add,map_mul,map_pow,aeval_X,aeval_C,
    sub_eq_zero] using h

/-- A full set of simple roots in the splitting field still accounts for
every root after any field embedding into a larger residue field. -/
private theorem root_from_splitting_field {P : F[X]} {d : ℕ} (A : FibreAction P d)
    {L : Type*} [Field L] (ψ : P.SplittingField →+* L) (nz : P ≠ 0) (z : L)
    (hz : (P.map (ψ.comp (algebraMap F P.SplittingField))).IsRoot z) :
    ∃ j, ψ (A.label j).val = z := by
  classical
  have h := (mem_roots (Polynomial.map_ne_zero nz)).mpr hz
  rw [← Polynomial.map_map, roots_map ψ
    ((splits_id_iff_splits _).mpr (SplittingField.splits P))] at h
  obtain ⟨t,ht,htz⟩ := Multiset.mem_map.mp h
  have rt : t ∈ P.rootSet P.SplittingField := Multiset.mem_toFinset.mpr ht
  refine ⟨A.label.symm ⟨t,rt⟩,?_⟩
  rw [Equiv.apply_symm_apply]
  exact htz

variable [DecidableEq F]

private theorem conjugacy_of_reduction {d : ℕ} {P : F[X]} (nz : P ≠ 0) (sep : P.Separable)
    (A : FibreAction P d) (γ : Equiv.Perm (Fin d))
    {B L : Type*} [CommRing B] [IsDomain B] [Field L] (U : B[X]) (res : B →+* L)
    (coeff : AlgebraicClosure F →+* L) (t : Fin d → B) (inj : Function.Injective t)
    (rt : ∀ i, U.eval (t i) = 0) (red : U.map res = P.map (coeff.comp (algebraMap F _)))
    (v : L → L) (vm : ∀ i, res (t (γ i)) = v (res (t i)))
    (vc : ∀ c, v (coeff c) = coeff (c ^ Fintype.card F)) : IsConj A.perm γ := by
  classical
  have rroot (i : Fin d) : (U.map res).IsRoot (res (t i)) := by
    rw [IsRoot.def,eval_map,eval₂_at_apply,rt,map_zero]
  have r_inj : Function.Injective (fun i => res (t i)) := by
    intro i j eq
    have simple : res (U.derivative.eval (t i)) ≠ 0 := by
      rw [←eval₂_at_apply,←eval_map,←derivative_map]
      have hs : (U.map res).Separable := red ▸ sep.map
      exact hs.eval₂_derivative_ne_zero (RingHom.id _) (by simpa using rroot i)
    exact inj (eq_of_common_simple_reduction res (rt i) (rt j) eq simple)
  let emb := IsAlgClosed.lift (R := F) (S := P.SplittingField) (M := AlgebraicClosure F)
  let ψ := coeff.comp emb.toRingHom
  have φeq : ψ.comp (algebraMap F P.SplittingField) = coeff.comp (algebraMap F _) :=
    RingHom.ext fun c => congrArg coeff (emb.commutes c)
  have values (i : Fin d) : ∃ j, ψ (A.label j).val = res (t i) := by
    apply root_from_splitting_field A ψ nz _
    rw [φeq,←red]
    exact rroot i
  choose matchRoot matched using values
  have inj' : Function.Injective matchRoot := by
    intro i j eq
    apply r_inj
    change res (t i) = res (t j)
    rw [←matched i,←matched j,eq]
  let s := Equiv.ofBijective matchRoot ⟨inj',Finite.surjective_of_injective inj'⟩
  have step (i : Fin d) : s (γ i) = A.perm (s i) := by
    apply A.label.injective
    apply Subtype.ext
    apply ψ.injective
    rw [A.frobenius,map_pow]
    calc
      _ = res (t (γ i)) := matched _
      _ = v (res (t i)) := vm i
      _ = v (ψ (A.label (s i)).val) := congrArg v (matched i).symm
      _ = ψ (A.label (s i)).val ^ Fintype.card F := (vc (emb _)).trans (map_pow _ _ _)
  apply isConj_iff.mpr
  refine ⟨s.symm, Equiv.ext fun i => ?_⟩
  change s.symm (A.perm (s i)) = γ i
  rw [←step, Equiv.symm_apply_apply]

private theorem integralFibre_aeval {M : Type*} [Field M] (O : ValuationSubring M)
    (x : M) (a v : O) (d : ℕ) (eqn : x^d = (a : M)*x^(d-1)+(v : M)) :
    aeval x (integralFibre d a v) = 0 := by
  simpa only [integralFibre,map_sub,map_add,map_mul,map_pow,aeval_X,aeval_C,
    ValuationSubring.algebraMap_apply,sub_eq_zero] using eqn

/-- At an unexcluded rational intercept the permutation of the generic
sheets specializes to the q-power permutation of the fibre, up to conjugacy.
The only local input is a stable valuation ring above the intercept. -/
theorem specialization_of_stable_place {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F) (g : geomAut d a S) {b : F} (hb : some b ∉ excludedBranches d a S)
    (p : StableTwistPlace d a S g b) (α : S) :
    IsConj (regularFibreAction hd ha S hb α).perm
      ((frobeniusRootAction hd ha S * geometricRootAction hd ha S g) α) := by
  classical
  let k := AlgebraicClosure F
  let f := algebraMap F k
  let O := p.ring
  let res := LocalRing.residue O
  let lift := p.over.constants
  let P := lineFibre d a (b+α.val)
  let A := regularFibreAction hd ha S hb α
  let γ := (frobeniusRootAction hd ha S * geometricRootAction hd ha S g) α
  let U : O[X] := integralFibre d (lift (f a)) (p.over.parameter + lift (f α.val))
  let gener (i : Fin d) := (rootLabel hd ha S α i).val
  have root (i : Fin d) : aeval (gener i) U = 0 := by
    apply integralFibre_aeval
    change _ = (lift (f a) : geom d a S)*_ + ((p.over.parameter : geom d a S) + lift (f α.val))
    rw [p.over.parameter_lift]
    simpa only [lift,p.over.constants_lift] using labelled_root_equation hd ha S α i
  let t (i : Fin d) : O := ⟨gener i,monic_root_mem_valuation O (integralFibre_monic (by omega) _ _) (root i)⟩
  have rt (i : Fin d) : U.eval (t i) = 0 := by
    apply IsFractionRing.injective O (geom d a S)
    rw [map_zero,← aeval_algebraMap_apply_eq_algebraMap_eval]
    exact root i
  let φ := (res.comp lift).comp f
  have par : res p.over.parameter = (res.comp lift) (f b) := by
    simpa [res,lift,f] using p.over.specializes
  have red : U.map res = P.map φ := by
    simp only [U,P,integralFibre,lineFibre,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_pow,map_X,map_C,map_add,par]
    rfl
  let τ := g.toRingEquiv.trans (geometricFrobenius d a S)
  let v := restrictRing O τ p.stable
  let vbar := LocalRing.ResidueField.mapEquiv v
  have vbar_const (c : k) : vbar ((res.comp lift) c) = (res.comp lift) (c^Fintype.card F) := by
    change res (v (lift c)) = res (lift _)
    apply congrArg res
    apply Subtype.ext
    change geometricFrobenius d a S (g (p.over.constants c : geom d a S)) = (p.over.constants _ : geom d a S)
    rw [p.over.constants_lift,p.over.constants_lift,component_constants]
  have vm (i : Fin d) : v (t i) = t (γ i) := Subtype.ext (frobenius_coset_action hd ha S g α i).symm
  exact conjugacy_of_reduction (integralFibre_monic (by omega : 2 ≤ d) _ _).ne_zero
    (unexcluded_separable hd ha S hb α) A γ U res (res.comp lift) t
    (fun i j eq => (rootLabel hd ha S α).injective (Subtype.ext (congrArg (fun z : O => (z : geom d a S)) eq)))
    rt red vbar (fun i => congrArg res (vm i).symm) vbar_const

/-- A chart on the geometric cover defined over a rational place of the
descended field. Its specialization is evaluated in the geometric constants. -/
structure TwistReductionChart {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F) (g : geomAut d a S) (b : F) where
  ring : Subring (geom d a S)
  constants : AlgebraicClosure F →+* ring
  constants_lift : ∀ c, (constants c : geom d a S) = algebraMap _ _ (RatFunc.C c)
  parameter : ring
  parameter_lift : (parameter : geom d a S) = algebraMap (RatFunc (AlgebraicClosure F)) _ RatFunc.X
  residue : ring →+* AlgebraicClosure F
  on_constants : ∀ c, residue (constants c) = c
  at_parameter : residue parameter = algebraMap F (AlgebraicClosure F) b
  sheet_mem : ∀ α i, (rootLabel hd ha S α i).val ∈ ring
  equivariant : ∀ x y : ring, (y : geom d a S) = geometricFrobenius d a S (g x) →
    residue y = residue x ^ Fintype.card F

/-- On the regular locus an equivariant homomorphism on a chart containing
the sheets proves the specialization law on their canonical labels. -/
theorem specialization_of_chart {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F) (g : geomAut d a S) {b : F} (hb : some b ∉ excludedBranches d a S)
    (p : TwistReductionChart hd ha S g b) (α : S) :
    IsConj (regularFibreAction hd ha S hb α).perm
      ((frobeniusRootAction hd ha S * geometricRootAction hd ha S g) α) := by
  let k := AlgebraicClosure F
  let f := algebraMap F k
  let U := integralFibre d (p.constants (f a)) (p.parameter + p.constants (f α.val))
  let t (i : Fin d) : p.ring := ⟨(rootLabel hd ha S α i).val, p.sheet_mem α i⟩
  have rt (i : Fin d) : U.eval (t i) = 0 := by
    simp only [U,integralFibre,eval_sub,eval_add,eval_mul,eval_pow,eval_X,eval_C,sub_eq_zero]
    apply Subtype.ext
    change _ = (p.constants (f a) : geom d a S)*_ +
      ((p.parameter : geom d a S) + (p.constants (f α.val) : geom d a S))
    rw [p.parameter_lift,p.constants_lift,p.constants_lift]
    exact labelled_root_equation hd ha S α i
  have red : U.map p.residue = (lineFibre d a (b+α.val)).map ((RingHom.id k).comp f) := by
    simp only [U,integralFibre,lineFibre,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_pow,map_X,map_C,map_add,p.on_constants,p.at_parameter,RingHom.id_comp]
  apply conjugacy_of_reduction (integralFibre_monic (by omega : 2 ≤ d) _ _).ne_zero
    (unexcluded_separable hd ha S hb α) _ _ U p.residue (RingHom.id k) t
    (fun i j eq => (rootLabel hd ha S α).injective
      (Subtype.ext (congrArg (fun z : p.ring => (z : geom d a S)) eq))) rt red
    (fun z => z^Fintype.card F) _ (fun _ => rfl)
  intro i
  exact p.equivariant _ _ (frobenius_coset_action hd ha S g α i)

end
end BlockingCurves.CuspidalGeneral
