import PencilHorizontal
import Frobenius
import Mathlib.FieldTheory.Separable
import Mathlib.Combinatorics.Derangements.Exponential

/-! The finite-field Frobenius actually acting on a regular fibre, and the
Chebotarev input for the derangement leading coefficient. -/
namespace BlockingCurves.PencilSampling
open Finset Polynomial Real Filter
open scoped Topology

noncomputable def derangementFraction (d : ℕ) : ℝ :=
  (Fintype.card (derangements (Fin d)):ℝ)/Fintype.card (Equiv.Perm (Fin d))

theorem derangementFraction_eq (d : ℕ) :
    derangementFraction d = (numDerangements d:ℝ)/d.factorial := by
  rw [derangementFraction,card_derangements_fin_eq_numDerangements,Fintype.card_perm,Fintype.card_fin]

theorem derangement_coefficient_limit :
    Tendsto (fun d => 2/log (1/derangementFraction d)) atTop (𝓝 2) := by
  have hd : Tendsto derangementFraction atTop (𝓝 (exp (-1))) := by
    simpa only [_root_.funext derangementFraction_eq] using numDerangements_tendsto_inv_e
  have h := (tendsto_const_nhds.div hd (exp_ne_zero _)).log
    (div_ne_zero one_ne_zero (exp_ne_zero (-1)))
  have hlim : log (1 / exp (-1)) = 1 := by rw [one_div,← exp_neg,neg_neg,log_exp]
  rw [hlim] at h
  simpa using (tendsto_const_nhds (x := (2:ℝ))).div h one_ne_zero

theorem derangementFraction_bounds {d : ℕ} (hd : 2 ≤ d) :
    0 < derangementFraction d ∧ derangementFraction d < 1 := by
  have hp : ∀ n : ℕ, 0 < numDerangements (n+2) := by
    intro n; induction n with
    | zero => decide
    | succ n ih =>
      rw [numDerangements_add_two (n+1)]
      exact Nat.mul_pos (by omega) (Nat.add_pos_right _ ih)
  have h1 : 0 < Fintype.card (derangements (Fin d)) := by
    rw [card_derangements_fin_eq_numDerangements]
    obtain ⟨k,rfl⟩ : ∃ k, d=k+2 := ⟨d-2,by omega⟩
    exact hp k
  have hlt : Fintype.card (derangements (Fin d)) < Fintype.card (Equiv.Perm (Fin d)) :=
    Fintype.card_subtype_lt (p := derangements (Fin d)) (x := Equiv.refl (Fin d))
      (fun h => h ⟨0,by omega⟩ rfl)
  unfold derangementFraction
  constructor
  · exact div_pos (by exact_mod_cast h1) (by exact_mod_cast h1.trans hlt)
  · exact (div_lt_one (by exact_mod_cast h1.trans hlt)).2 (by exact_mod_cast hlt)

variable {F : Type*} [Field F] [Fintype F]
noncomputable local instance : DecidableEq F := Classical.decEq _

noncomputable def fibre (d : ℕ) (m t : F) : F[X] := X^d-(C m*X+C t)

theorem fibre_degree {d : ℕ} (hd : 2 ≤ d) (m t : F) : (fibre d m t).natDegree=d := by
  have hl : (C m*X+C t).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans (max_le _ _)
    · exact natDegree_mul_le.trans (by simp)
    · simp
  rw [fibre,natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega),natDegree_X_pow]

/-- Labelled action of arithmetic Frobenius on every geometric root of P in
its splitting field. The characteristic-power equation fixes its cycle type. -/
structure FibreAction (P : F[X]) (d : ℕ) where
  label : Fin d ≃ P.rootSet P.SplittingField
  perm : Equiv.Perm (Fin d)
  frobenius : ∀ i, ((label (perm i)).val) = (label i).val ^ Fintype.card F

noncomputable def fibreAction {P : F[X]} {d : ℕ} (hs : P.Separable) (hd : P.natDegree=d) :
    FibreAction P d := by
  classical
  let K := P.SplittingField
  letI : Fintype K := Module.fintypeOfFintype (FiniteDimensional.finBasis F K)
  let e := (Fintype.equivFinOfCardEq ((card_rootSet_eq_natDegree hs
    (SplittingField.splits P)).trans hd)).symm
  let σ := (exists_card_frobenius F K).choose
  have hf := (exists_card_frobenius F K).choose_spec
  let f (i : Fin d) := e.symm ⟨σ (e i).val, rootSet_mapsTo σ.toAlgHom (e i).property⟩
  have eqn (i : Fin d) : (e (f i)).val = σ (e i).val := by simp [f]
  have hin : Function.Injective f := by
    intro i j h
    apply e.injective
    apply Subtype.ext
    apply σ.injective
    rw [← eqn,← eqn,h]
  exact ⟨e,Equiv.ofBijective f ⟨hin,Finite.surjective_of_injective hin⟩,
    fun i => (eqn i).trans (hf _)⟩

theorem frobenius_derangement_iff {d : ℕ} (hd : 2 ≤ d) (m t : F)
    (A : FibreAction (fibre d m t) d) :
    A.perm ∈ derangements (Fin d) ↔ ¬ ∃ x : F, x^d-m*x=t := by
  let P := fibre d m t
  let K := P.SplittingField
  letI : Fintype K := Module.fintypeOfFintype (FiniteDimensional.finBasis F K)
  have hP : P ≠ 0 := fun h => by
    have hdeg : P.natDegree=d := fibre_degree hd _ _
    rw [h,natDegree_zero] at hdeg; omega
  have hroot (x : F) : algebraMap F K x ∈ P.rootSet K ↔ x^d-m*x=t := by
    rw [mem_rootSet_of_ne hP,aeval_algebraMap_apply]
    simp [P,fibre,sub_eq_zero]
    rw [← map_pow,← map_mul,← map_add,(algebraMap F K).injective.eq_iff]
    constructor <;> intro h <;> linear_combination h
  constructor
  · rintro h ⟨x,hx⟩
    let z : P.rootSet K := ⟨algebraMap F K x,(hroot x).2 hx⟩
    let i := A.label.symm z
    apply h i
    apply A.label.injective
    apply Subtype.ext
    rw [A.frobenius,show A.label i=z by simp [i]]
    exact (pow_card_eq_iff_scalar F K _).2 ⟨x,rfl⟩
  · intro h i hi
    have hf : (A.label i).val ^ Fintype.card F=(A.label i).val :=
      (A.frobenius i).symm.trans (congrArg (fun j => (A.label j).val) hi)
    obtain ⟨x,hx⟩ := (pow_card_eq_iff_scalar F K _).1 hf
    exact h ⟨x,(hroot x).1 (hx ▸ (A.label i).property)⟩


noncomputable def regular (d : ℕ) (m : F) : Finset F := by
  classical
  exact univ.filter fun t => (fibre d m t).Separable

private theorem multiple_root {P : F[X]} (hP : P ≠ 0) (hs : ¬P.Separable) :
    ∃ z : AlgebraicClosure F, aeval z P=0 ∧ aeval z (derivative P)=0 := by
  classical
  by_contra! h
  apply hs
  apply EuclideanDomain.isCoprime_of_dvd (fun he => hP he.1)
  rintro g hg _ ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) g
    (fun h0 => hg (isUnit_iff_degree_eq_zero.mpr h0))
  apply h z (by rw [ha,map_mul,hz,zero_mul])
  rw [hb,map_mul,hz,zero_mul]

/-- The exceptional rational parameters inject into the geometric roots of
the common derivative. For nonzero slopes this even holds when p divides d. -/
theorem exceptional_fibres_le {d : ℕ} (hd : 2 ≤ d) (m : F) (hm : m ≠ 0) :
    ((univ : Finset F) \ regular d m).card ≤ d-1 := by
  classical
  let K := AlgebraicClosure F
  let D : F[X] := C (d:F)*X^(d-1)-C m
  have hD : D ≠ 0 := by
    intro hz
    have := congrArg (eval (0:F)) hz
    simp [D,zero_pow (show d-1≠0 by omega)] at this
    exact hm this
  have hDdeg : D.natDegree ≤ d-1 := by
    apply (natDegree_sub_le _ _).trans (max_le _ _)
    · exact natDegree_mul_le.trans (by simp)
    · simp
  have dx (t : F) : derivative (fibre d m t)=D := by
    simp [fibre,D,derivative_X_pow,derivative_sub,derivative_add,derivative_mul]
  let B := (univ : Finset F) \ regular d m
  have ex (t : B) : ∃ z : K, aeval z (fibre d m t.val)=0 ∧ aeval z D=0 := by
    have hn : ¬(fibre d m t.val).Separable := by
      have ht := (mem_sdiff.mp t.property).2
      simpa [regular] using ht
    have hp : fibre d m t.val ≠ 0 := fun he => by
      have h := fibre_degree hd m t.val; rw [he,natDegree_zero] at h; omega
    simpa [dx t.val] using multiple_root hp hn
  let f (t : B) : D.rootSet K := ⟨(ex t).choose,(mem_rootSet_of_ne hD).2 (ex t).choose_spec.2⟩
  have hi : Function.Injective f := by
    intro t u he
    have h := congrArg Subtype.val he
    have ht := (ex t).choose_spec.1
    have hu := (ex u).choose_spec.1
    change (ex t).choose=(ex u).choose at h
    rw [h] at ht
    simp [fibre] at ht hu
    apply Subtype.ext
    apply (algebraMap F K).injective
    linear_combination hu-ht
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe] at hc
  apply hc.trans
  change Fintype.card ((D.aroots K).toFinset : Type _) ≤ _
  rw [Fintype.card_coe]
  exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans
    ((natDegree_map_le _ _).trans hDdeg))

/-- Value on the branch locus is ignored by the counting input. -/
noncomputable def frobPerm {d : ℕ} (hd : 2 ≤ d) (m t : F) : Equiv.Perm (Fin d) := by
  classical
  exact if h : (fibre d m t).Separable then (fibreAction h (fibre_degree hd m t)).perm else 1

/-- Finite Chebotarev on the regular affine base, for a conjugacy-invariant
union in S_d. The bound is expressed directly as a count error in units √q. -/
def Stable (D : Finset (Equiv.Perm (Fin d))) : Prop :=
  ∀ σ ∈ D, ∀ g : Equiv.Perm (Fin d), g*σ*g⁻¹ ∈ D

noncomputable def frobCount {d : ℕ} (hd : 2 ≤ d) (m : F) (D : Finset (Equiv.Perm (Fin d))) : ℕ := by
  classical
  exact ((regular d m).filter (fun t => frobPerm hd m t ∈ D)).card

def ChebotarevUpper (F : Type*) [Field F] [Fintype F] {d : ℕ} (hd : 2 ≤ d) (A : ℝ) : Prop :=
  ∀ m : Fˣ, ∀ D : Finset (Equiv.Perm (Fin d)), Stable D →
    (frobCount hd (m:F) D:ℝ) ≤ (regular d (m:F)).card *
      ((D.card:ℝ)/Fintype.card (Equiv.Perm (Fin d))) + A*sqrt (Fintype.card F)

private lemma stable_derangements (d : ℕ) : Stable ((derangements (Fin d)).toFinset) := by
  classical
  intro σ hσ g
  have h := Set.mem_toFinset.mp hσ
  apply Set.mem_toFinset.mpr
  intro i he
  apply h (g⁻¹ i)
  apply g.injective
  simpa using he

/-- The standard count on regular fibres supplies the missing-value estimate
for every intercept, with the exceptional fibres explicitly absorbed. -/
theorem line_miss_of_chebotarev {d : ℕ} (hd : 2 ≤ d) {A : ℝ}
    (hCheb : ChebotarevUpper F hd A) (l : Fˣ × F) :
    ((missed d (.inr l : Lines F)).card:ℝ) ≤ Fintype.card F *
      (derangementFraction d + (A+(d-1:ℕ))/sqrt (Fintype.card F)) := by
  classical
  let m : F := l.1
  let D := (derangements (Fin d)).toFinset
  let B := (univ : Finset F) \ regular d m
  let T := (regular d m).filter (fun t => frobPerm hd m t ∈ D)
  have inc : (missed d (.inr l : Lines F)).image (fun a => a+l.2) ⊆ T ∪ B := by
    rintro t ht
    obtain ⟨a,ha,rfl⟩ := mem_image.mp ht
    by_cases hr : a+l.2 ∈ regular d m
    · apply mem_union_left _ (mem_filter.mpr ⟨hr,?_⟩)
      have hs : (fibre d m (a+l.2)).Separable := (mem_filter.mp hr).2
      rw [frobPerm,dif_pos hs]
      apply Set.mem_toFinset.mpr
      apply (frobenius_derangement_iff hd m _ _).2
      rintro ⟨x,hx⟩
      apply (mem_filter.mp ha).2
      exact ⟨x,by change x^d-m*x-l.2=a; linear_combination hx⟩
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_univ _,hr⟩)
  have hc := (card_le_card inc).trans (card_union_le T B)
  rw [card_image_of_injective _ (add_left_injective _)] at hc
  have hh : (missed d (.inr l : Lines F)).card ≤ frobCount hd m D+(d-1) :=
    hc.trans (Nat.add_le_add_left (exceptional_fibres_le hd m l.1.ne_zero) _)
  have hu := hCheb l.1 D (stable_derangements d)
  have hD : (D.card:ℝ)/Fintype.card (Equiv.Perm (Fin d)) = derangementFraction d := by
    rw [derangementFraction,show D.card=Fintype.card (derangements (Fin d)) from Set.toFinset_card _]
  rw [hD] at hu
  have hr : ((regular d m).card:ℝ) ≤ Fintype.card F := by exact_mod_cast card_le_univ (regular d m)
  have hh' : ((missed d (.inr l : Lines F)).card:ℝ) ≤ frobCount hd m D+((d-1:ℕ):ℝ) := by exact_mod_cast hh
  have hq : (2:ℝ) ≤ Fintype.card F := by exact_mod_cast (show 2 ≤ Fintype.card F from Fintype.one_lt_card)
  have hs : 1 ≤ sqrt (Fintype.card F) := (le_sqrt (by norm_num) (by positivity)).2 (by linarith)
  have hpos : 0 < sqrt (Fintype.card F) := by linarith
  have he : (Fintype.card F:ℝ)/sqrt (Fintype.card F) = sqrt (Fintype.card F) := by
    rw [div_eq_iff hpos.ne',← sq,sq_sqrt (by positivity)]
  have hcost := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (d-1) : (0:ℝ) ≤ (d-1:ℕ))
  have hr' := mul_le_mul_of_nonneg_right hr (derangementFraction_bounds hd).1.le
  change (frobCount hd m D:ℝ) ≤ (regular d m).card*derangementFraction d+A*sqrt (Fintype.card F) at hu
  rw [mul_add, mul_div_left_comm,he]
  linarith only [hh',hu,hr',hcost]



/-- A single Frobenius conjugacy class. -/
noncomputable def permClass {d : ℕ} (c : ConjClasses (Equiv.Perm (Fin d))) :
    Finset (Equiv.Perm (Fin d)) := by
  classical
  exact univ.filter (fun σ => ConjClasses.mk σ = c)

/-- It suffices to supply one standard effective Chebotarev bound per class.
Summation over the classes in a given union costs at most d! times the
largest one-class error constant. -/
theorem chebotarevUpper_of_classes {d : ℕ} (hd : 2 ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ (m : Fˣ) (c : ConjClasses (Equiv.Perm (Fin d))),
      (frobCount hd (m:F) (permClass c):ℝ) ≤ (regular d (m:F)).card *
        (((permClass c).card:ℝ)/Fintype.card (Equiv.Perm (Fin d))) + A*sqrt (Fintype.card F)) :
    ChebotarevUpper F hd (d.factorial*A) := by
  classical
  intro m D hD
  let J := D.image ConjClasses.mk
  have hmem (σ : Equiv.Perm (Fin d)) : ConjClasses.mk σ ∈ J ↔ σ ∈ D := by
    constructor
    · intro h
      obtain ⟨τ,hτ,he⟩ := mem_image.mp h
      obtain ⟨g,hg⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
      exact hg ▸ hD τ hτ g
    · intro h; exact mem_image_of_mem _ h
  have hpc : ∑ c ∈ J, (permClass c).card = D.card := by
    change ∑ c ∈ J, (univ.filter (fun τ : Equiv.Perm (Fin d) => ConjClasses.mk τ=c)).card = _
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext σ
    simp only [mem_filter,mem_univ,true_and,hmem]
  have hfc : ∑ c ∈ J, frobCount hd (m:F) (permClass c) = frobCount hd (m:F) D := by
    simp only [frobCount,permClass,mem_filter,mem_univ,true_and]
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    ext t
    simp only [mem_filter,hmem]
  have hJ : (J.card:ℝ) ≤ (d.factorial:ℝ) := by
    exact_mod_cast (card_image_le.trans (card_le_univ D)).trans_eq
      (by rw [Fintype.card_perm,Fintype.card_fin])
  have hsum := sum_le_sum (s := J) (fun c _ => h m c)
  rw [sum_add_distrib,← mul_sum,← sum_div,sum_const,nsmul_eq_mul,
    ← Nat.cast_sum,← Nat.cast_sum,hpc,hfc] at hsum
  apply hsum.trans
  apply add_le_add_left
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_right hJ (by positivity)

/-- Full projective coefficient with the derangement proportion in S_d,
with all deductions after the Chebotarev input formalized. -/
theorem projective_upper_of_chebotarev {d : ℕ} (hd : 2 ≤ d) {A : ℝ} (hA : 0 ≤ A)
    (h : ChebotarevUpper F hd A)
    (hsize : 2*((A+(d-1:ℕ))/derangementFraction d) ≤
      log (1/derangementFraction d)*sqrt (Fintype.card F)) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ sampleCutoff (Fintype.card F) (1/2)
        (horizontalRate (d.gcd (Fintype.card F-1)) (log (1/derangementFraction d)))
        (log (1/derangementFraction d)) ((A+(d-1:ℕ))/derangementFraction d) + 1 :=
  projective_upper_of_nonzero_value_set hd (derangementFraction_bounds hd).1 (derangementFraction_bounds hd).2
    (by positivity) hsize (line_miss_of_chebotarev hd h)



/-- Projective second-order bound with the same class count and a separate
geometric common-parameter theorem on the residual lines. -/
theorem projective_loglog_of_chebotarev {d : ℕ} (hd : 2 ≤ d) {c A : ℝ}
    (hc : 0 < c) (hz : 1/2 ≤ c*log (Fintype.card F)) (hzq : c*log (Fintype.card F) ≤ Fintype.card F)
    (hA : 0 ≤ A) (h : ChebotarevUpper F hd A)
    (hsize : 2*((A+(d-1:ℕ))/derangementFraction d) ≤
      log (1/derangementFraction d)*sqrt (Fintype.card F))
    (hcommon : CommonHit F d ⌊c*log (Fintype.card F)⌋₊) :
    ∃ S : Finset F, ProjectiveBlocks d (S : Set F) ∧
      (S.card:ℝ) ≤ max
        ((log (Fintype.card F)-log (log (Fintype.card F))-log c+log 2)/
          horizontalRate (d.gcd (Fintype.card F-1)) (log (1/derangementFraction d)))
        ((2*log (Fintype.card F)-log (log (Fintype.card F))-log c+log 2)/
          log (1/derangementFraction d)
          + 12*((A+(d-1:ℕ))/derangementFraction d)/(log (1/derangementFraction d))^2) + 2 :=
  projective_loglog_of_nonzero_value_set hd hc hz hzq (derangementFraction_bounds hd).1
    (derangementFraction_bounds hd).2 (by positivity) hsize (line_miss_of_chebotarev hd h) hcommon


end BlockingCurves.PencilSampling
