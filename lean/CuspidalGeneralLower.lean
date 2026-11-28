import CuspidalGeneralBranch
import CuspidalGeneralInertia
import CuspidalTowerBudget
import PencilFrobeniusCount

/-! The lower bound from geometric inertia and ordinary rational-point data
on a Frobenius twist. No density, missed-line count or derangement is an input. -/
namespace BlockingCurves.CuspidalGeneral

open Finset Polynomial PencilSampling

variable {F : Type*} [Field F] [Fintype F]

noncomputable def lineFibre (d : ℕ) (a v : F) : F[X] :=
  X^d-(C a*X^(d-1)+C v)

private theorem lineFibre_nonzero {d : ℕ} (hd : 2 ≤ d) (a v : F) :
    lineFibre d a v≠0 := by
  have degree : (C a*X^(d-1)+C v : F[X]).natDegree ≤ d-1 := by
    apply natDegree_add_le_of_degree_le
    · simpa using natDegree_C_mul_le a ((X:F[X])^(d-1))
    · simp
  apply sub_ne_zero.mpr
  intro h
  have := congrArg natDegree h
  rw [natDegree_X_pow] at this
  omega

/-- An actual rational root of a specialized cusp polynomial forces a fixed
letter in the labelled Frobenius permutation on its splitting-field roots. -/
theorem rational_root_fixed {d : ℕ} (hd : 2 ≤ d) (a v t : F)
    (A : FibreAction (lineFibre d a v) d) (root : t^d-a*t^(d-1)=v) :
    ∃ i, A.perm i=i := by
  let P := lineFibre d a v
  let K := P.SplittingField
  letI : Fintype K := Module.fintypeOfFintype (FiniteDimensional.finBasis F K)
  have eval : P.eval t=0 := by
    simp only [P,lineFibre,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_C]
    linear_combination root
  have hz : algebraMap F K t ∈ P.rootSet K := by
    rw [mem_rootSet_of_ne (lineFibre_nonzero hd a v),aeval_algebraMap_apply_eq_algebraMap_eval,
      eval,map_zero]
  let z : P.rootSet K := ⟨algebraMap F K t,hz⟩
  let i := A.label.symm z
  refine ⟨i,A.label.injective (Subtype.ext ?_)⟩
  rw [A.frobenius,show A.label i=z by simp [i]]
  exact (pow_card_eq_iff_scalar F K _).2 ⟨t,rfl⟩

/-- Finite rational-point data supplied by the function-field twist.
Its fibre actions are on actual splitting fields and use the field-size
Frobenius, as prescribed by 'PencilSampling.FibreAction'. The geometric
degree, genus, point-count and specialization facts are recorded separately. -/
structure TwistPointData [DecidableEq F] (d : ℕ) (a : F) (S : Finset F)
    (γ : S → Equiv.Perm (Fin d)) where
  points : ℕ
  genus : ℕ
  degree : ℕ
  projection : Fin points → Option F
  branch : Finset (Option F)
  infinity : none ∈ branch
  branch_size : branch.card ≤ 2*S.card+1
  hasse_weil : (Fintype.card F:ℝ)+1-2*genus*Real.sqrt (Fintype.card F) ≤ points
  fibre_degree : ∀ b, (univ.filter fun p => projection p=b).card ≤ degree
  specialization : ∀ p b, projection p=some b → some b ∉ branch → ∀ α : S,
    ∃ A : FibreAction (lineFibre d a (b+α.val)) d, A.perm=γ α

/-- Rational points on a twist with the global estimates needed by the
finite threshold. A root tower supplies both estimates. -/
structure TwistPoints [DecidableEq F] (d : ℕ) (a : F) (S : Finset F)
    (γ : S → Equiv.Perm (Fin d)) extends TwistPointData d a S γ where
  degree_bound : degree ≤ d.factorial ^ S.card
  genus_bound : 2*genus ≤ S.card*(d-1)*degree

def TwistPointData.ofRootTower [DecidableEq F] {d : ℕ} (hd : 0<d) {a : F}
    {S : Finset F} {γ : S → Equiv.Perm (Fin d)} (P : TwistPointData d a S γ)
    (T : CuspidalTower.RootTower d S.card)
    (genus : P.genus=T.genus S.card 0) (degree : P.degree=T.degree S.card 0) :
    TwistPoints d a S γ where
  toTwistPointData := P
  degree_bound := degree ▸ CuspidalTower.degree_budget T
  genus_bound := by
    rw [genus,degree]
    have := CuspidalTower.genus_budget hd T
    have := T.positive S.card le_rfl 0 (Nat.zero_le _)
    omega

/-- From the local inertia orbit data and geometric twists to the sharp
factorial-base finite threshold for an actual set blocking the cusp pencil. -/
theorem lower_of_inertia_twists [DecidableEq F] {d : ℕ} (hd : 3 ≤ d)
    (S : Finset F) (a : F) (H : Subgroup (S → Equiv.Perm (Fin d)))
    (trans : ∀ i x u, ∃ h : H, h.val i x=u)
    (inertia : ∀ i, ∃ x₀ : Fin d, ∀ y z : Fin d, y≠x₀ → z≠x₀ →
      ∃ h : H, (∀ j, j≠i → h.val j=1) ∧ h.val i x₀=x₀ ∧ h.val i y=z)
    (σ : S → Equiv.Perm (Fin d))
    (twist : ∀ h : H, Nonempty (TwistPoints d a S (σ*h.val)))
    (hq : 16 ≤ (Fintype.card F:ℝ)) (blocks : Blocks d (S:Set F)) :
    (Real.log (Fintype.card F)-2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial:ℝ)) - Real.log (16*(d:ℝ))/Real.log (d.factorial:ℝ) < S.card := by
  classical
  letI : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨h,der⟩ := independent_inertia_derangements
    (by simpa only [Fintype.card_fin] using (show 2<d by omega)) H trans inertia σ
  obtain ⟨T⟩ := twist h
  by_contra! small
  have deg : 2 ≤ (d.factorial:ℝ) := by
    exact_mod_cast (show 2 ≤ d.factorial from Nat.factorial_le (show 2 ≤ d by omega))
  have dpos : 1 ≤ (d:ℝ) := by exact_mod_cast (show 1≤d by omega)
  have gb : (T.genus:ℝ) ≤ S.card*((d:ℝ)-1)*(d.factorial:ℝ)^S.card := by
    have hg := T.genus_bound.trans (Nat.mul_le_mul_left _ T.degree_bound)
    have gd : T.genus ≤ S.card*(d-1)*d.factorial^S.card := by omega
    rw [←Nat.cast_one (R:=ℝ),←Nat.cast_sub (by omega : 1 ≤ d)]
    exact_mod_cast gd
  have num := twist_threshold hq deg dpos gb small
  have count : (2*S.card+1)*d.factorial^S.card < T.points := by
    exact_mod_cast num.trans_le T.hasse_weil
  have good : ∃ p, T.projection p ∉ T.branch := by
    by_contra! all
    have pcount := card_le_mul_card_image (f:=T.projection) univ T.degree
      (fun b _ => T.fibre_degree b)
    have inc : univ.image T.projection ⊆ T.branch := by
      intro b hb
      obtain ⟨p,_,rfl⟩ := mem_image.mp hb
      exact all p
    simp only [card_univ,Fintype.card_fin] at pcount
    have cap := Nat.mul_le_mul T.degree_bound ((card_le_card inc).trans T.branch_size)
    rw [Nat.mul_comm (d.factorial^S.card)] at cap
    exact (not_le_of_gt count) (pcount.trans cap)
  obtain ⟨p,hp⟩ := good
  cases hb : T.projection p with
  | none => exact hp (hb ▸ T.infinity)
  | some b =>
    obtain ⟨t,ht⟩ := (blocks_iff (by omega : 2≤d) _).1 blocks a b
    let α : S := ⟨t^d-a*t^(d-1)-b,ht⟩
    obtain ⟨A,hA⟩ := T.specialization p b hb (hb ▸ hp) α
    have root : t^d-a*t^(d-1)=b+α.val := by dsimp [α]; ring
    obtain ⟨i,fixed⟩ := rational_root_fixed (by omega : 2≤d) _ _ _ A root
    rw [hA] at fixed
    exact (der α i) fixed

/-- Every Frobenius twist recovers the same geometric splitting field after
extension of constants. Identifying its degree and genus with the terminal
stage suffices: the numerical global degree and genus estimates are derived
once from the root tower. -/
theorem lower_of_inertia_root_tower [DecidableEq F] {d : ℕ} (hd : 3 ≤ d)
    (S : Finset F) (a : F) (H : Subgroup (S → Equiv.Perm (Fin d)))
    (trans : ∀ i x u, ∃ h : H, h.val i x=u)
    (inertia : ∀ i, ∃ x₀ : Fin d, ∀ y z : Fin d, y≠x₀ → z≠x₀ →
      ∃ h : H, (∀ j, j≠i → h.val j=1) ∧ h.val i x₀=x₀ ∧ h.val i y=z)
    (σ : S → Equiv.Perm (Fin d)) (T : CuspidalTower.RootTower d S.card)
    (twist : ∀ h : H, ∃ P : TwistPointData d a S (σ*h.val),
      P.genus=T.genus S.card 0 ∧ P.degree=T.degree S.card 0)
    (hq : 16 ≤ (Fintype.card F:ℝ)) (blocks : Blocks d (S:Set F)) :
    (Real.log (Fintype.card F)-2*Real.log (Real.log (Fintype.card F))) /
      (2*Real.log (d.factorial:ℝ)) - Real.log (16*(d:ℝ))/Real.log (d.factorial:ℝ) < S.card := by
  apply lower_of_inertia_twists hd S a H trans inertia σ _ hq blocks
  intro h
  obtain ⟨P,hg,hn⟩ := twist h
  exact ⟨P.ofRootTower (by omega) T hg hn⟩

end BlockingCurves.CuspidalGeneral
