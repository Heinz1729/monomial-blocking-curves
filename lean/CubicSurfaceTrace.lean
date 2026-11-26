import CubicPairCount
import CubicMonodromy
import CubicUnsigned
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Complex.Abs
import Mathlib.Tactic.FinCases

/-! Character expansion and geometric inputs for §§12–16. The finite count
uses the same punctures, cubic equations and ordered pairs as CubicPairCount. -/
namespace BlockingCurves.CubicSurfaceTrace
open Finset BigOperators
open CubicPairCount CubicCharacters

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Rational ordered points of the punctured configuration surface. -/
def points (S : Finset F) := ((S.image (fun a => -a))ᶜ).offDiag

private theorem mem_points (S : Finset F) (P : F × F) :
    P ∈ points S ↔ P.1 ≠ P.2 ∧ ∀ a ∈ S, P.1 ≠ -a ∧ P.2 ≠ -a := by
  have h (v : F) : v ∈ (S.image (fun a => -a))ᶜ ↔ ∀ a ∈ S, v ≠ -a := by
    simp only [mem_compl, mem_image, not_exists, not_and, ne_eq]
    exact forall_congr' fun a => forall_congr' fun _ => not_congr eq_comm
  rw [points, mem_offDiag, h, h]
  constructor
  · exact fun ⟨h₁, h₂, h₃⟩ => ⟨h₃, fun a ha => ⟨h₁ a ha, h₂ a ha⟩⟩
  · exact fun ⟨h₃, h₁₂⟩ => ⟨fun a ha => (h₁₂ a ha).1, fun a ha => (h₁₂ a ha).2, h₃⟩

theorem card_points (S : Finset F) :
    ((points S).card : ℝ) =
      ((Fintype.card F : ℝ) - S.card) * ((Fintype.card F : ℝ) - S.card - 1) := by
  have hs := S.card_le_univ
  have hneg : (S.image (fun a => -a)).card = S.card :=
    card_image_of_injective _ neg_injective
  simp only [points, offDiag_card, card_compl, hneg]
  cases h : Fintype.card F - S.card with
  | zero =>
    have e : S.card = Fintype.card F := by omega
    simp [e]
  | succ n =>
    have e : Fintype.card F = S.card + (n+1) := by omega
    rw [e]
    push_cast
    simp
    ring

/-- Number of rational roots in a coordinate of an ordered point. -/
def rootCount (P : F × F) (a : F) : ℕ :=
  (univ.filter fun x : F => x^3-3*x = parameter P.1 P.2 a).card

private theorem rootCount_zero (P : F × F) (a : F) :
    rootCount P a = 0 ↔ ∀ x : F, x^3-3*x ≠ parameter P.1 P.2 a := by
  simp [rootCount, card_eq_zero, Finset.eq_empty_iff_forall_not_mem]

theorem escape_as_filter (S : Finset F) :
    (points S).filter (fun P => ∀ a : S, rootCount P (a : F) = 0) = escapePairs S := by
  ext P
  simp only [mem_filter, mem_points, rootCount_zero, Subtype.forall, escapePairs, mem_univ,
    true_and, and_assoc]

section TensorTypes
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The coordinate choices with no sign character and with a prescribed unique sign. -/
private def unsignedWords (I : Type*) [Fintype I] [DecidableEq I] : Finset (Word I) :=
  Fintype.piFinset fun _ => {0, 2}
private def oneSign (i : I) : Finset (Word I) :=
  Fintype.piFinset fun j => if j = i then {1} else {0, 2}
private def signPair (t : Finset I) : Word I := fun i => if i ∈ t then 1 else 0

/-- Per-representation first Betti bound of §14. The three summands handle no
sign, exactly one sign, and two signs with all other coordinates trivial. -/
noncomputable def bettiCap (w : Word I) : ℝ :=
  (if w ∈ (unsignedWords I).erase 0 then 6 * (Fintype.card I : ℝ) + 2 else 0) +
  (∑ i, if w ∈ oneSign i then (2:ℝ) else 0) +
  ∑ t ∈ (univ : Finset I).powersetCard 2, if w = signPair t then 1 else 0

private theorem sum_members (s : Finset (Word I)) (c : ℝ) :
    (∑ w : Word I, if w ∈ s then c else 0) = s.card * c := by
  rw [← sum_filter]
  simp

private theorem no_sign_total :
    ((unsignedWords I).erase 0).card + 1 = 2 ^ Fintype.card I := by
  have h : (0 : Word I) ∈ unsignedWords I := by simp [unsignedWords, Fintype.mem_piFinset]
  rw [card_erase_add_one h, unsignedWords, Fintype.card_piFinset]
  simp [show (0 : Fin 3) ≠ 2 by decide]

private theorem one_sign_total (i : I) : (oneSign i).card * 2 = 2 ^ Fintype.card I := by
  rw [oneSign, Fintype.card_piFinset]
  have h (j : I) : (if j = i then ({1} : Finset (Fin 3)) else {0,2}).card =
      if j = i then 1 else 2 := by
    by_cases e : j = i <;> simp [e, show (0 : Fin 3) ≠ 2 by decide]
  simp_rw [h]
  rw [Finset.prod_ite]
  simp only [prod_const_one, one_mul, Finset.prod_const]
  have he : ((univ : Finset I).filter fun j => ¬j = i) = univ.erase i := by
    ext j
    simp
  rw [he, ← pow_succ, card_erase_add_one (mem_univ i), card_univ]

theorem sum_bettiCap :
    ∑ w : Word I, bettiCap w = CubicAsymptotics.highWeight (Fintype.card I) := by
  classical
  simp only [bettiCap, sum_add_distrib]
  rw [sum_members, Finset.sum_comm (s := (univ : Finset (Word I))) (t := (univ : Finset I)),
    Finset.sum_comm (s := (univ : Finset (Word I))) (t := (univ : Finset I).powersetCard 2)]
  simp_rw [sum_members]
  have h (i : I) : ((oneSign i).card : ℝ) * 2 = 2 ^ Fintype.card I := by
    exact_mod_cast one_sign_total i
  simp_rw [h]
  simp only [Finset.sum_ite_eq', mem_univ, if_true, sum_const, card_univ, card_powersetCard,
    nsmul_eq_mul, mul_one]
  have e : (((unsignedWords I).erase 0).card : ℝ) + 1 = 2 ^ Fintype.card I := by
    exact_mod_cast (no_sign_total (I := I))
  let n := Fintype.card I
  have hpair : (n.choose 2 : ℝ) * 2 = (n : ℝ) * (n - 1 : ℝ) := by
    cases n with
    | zero => norm_num
    | succ k =>
      have hh := Nat.choose_succ_right_eq (k+1) 1
      simp only [Nat.choose_one_right, Nat.add_sub_cancel] at hh
      push_cast
      rw [show (k:ℝ)+1-1 = k by ring]
      exact_mod_cast hh
  change _ + _ + (n.choose 2 : ℝ) = _
  unfold CubicAsymptotics.highWeight
  dsimp [n] at hpair
  nlinarith only [e, hpair, congrArg (fun t : ℝ => t * (6 * (Fintype.card I : ℝ) + 2)) e]

abbrev Positions {I : Type*} (w : Word I) := {j : I // w j = 2}
abbrev Coordinates {I : Type*} (w : Word I) := (Positions w → Bool) → ℂ

/-- The geometric information used by the meridian calculation consists of
generators, their commutations, and two matrix rows at each standard position. -/
structure MeridianModel (I : Type*) (G : Type*) [Group G] where
  loops : CubicCocycles.Meridians G (Option I)
  action : (w : Word I) → G →* Module.End ℂ (Coordinates w)
  sign : ∀ (w : Word I) (i : I), w i = 1 →
    CubicCocycles.SignAt loops (action w) (some i)
  xrow : ∀ (w : Word I) (j : Positions w) (f : Coordinates w) v,
    v j = true → action w (loops.x (some j.val)) f v = -f v
  yrow : ∀ (w : Word I) (j : Positions w) (f : Coordinates w) v,
    v j = false → action w (loops.y (some j.val)) f v = -f v
  xlocal : ∀ (w : Word I) (i : I) (j : Positions w), j.val ≠ i → ∀ f : Coordinates w,
    (∀ v, v j = false → f v = 0) → ∀ v, v j = false → action w (loops.x (some i)) f v = 0
  ylocal : ∀ (w : Word I) (i : I) (j : Positions w), j.val ≠ i → ∀ f : Coordinates w,
    (∀ v, v j = true → f v = 0) → ∀ v, v j = true → action w (loops.y (some i)) f v = 0

variable {G : Type*} [Group G]
noncomputable def meridianDim (M : MeridianModel I G) (w : Word I) :=
  FiniteDimensional.finrank ℂ (CubicCocycles.HOne (M.action w))

private theorem fixed_standard (M : MeridianModel I G) (w : Word I) (j : Positions w)
    (f : Coordinates w) (hx : M.action w (M.loops.x (some j.val)) f = f)
    (hy : M.action w (M.loops.y (some j.val)) f = f) : f = 0 := by
  funext v
  change f v = 0
  have h : f v = -f v := by
    cases h : v j with
    | true => simpa only [hx] using M.xrow w j f v h
    | false => simpa only [hy] using M.yrow w j f v h
  have z : 2 * f v = 0 := by rw [two_mul, ← sub_neg_eq_add, ← h, sub_self]
  exact (mul_eq_zero.mp z).resolve_left (by norm_num)

private theorem cap_nonneg (w : Word I) : 0 ≤ bettiCap w := by
  unfold bettiCap
  positivity

theorem meridian_bound (M : MeridianModel I G) (w : Word I)
    (hw : w ∈ nontrivialWords I) :
    (meridianDim M w : ℝ) ≤ bettiCap w := by
  classical
  by_cases hs : ∃ s, w s = 1
  · obtain ⟨s,hs⟩ := hs
    have S := M.sign w s hs
    by_cases ht : ∃ t, t ≠ s ∧ w t = 1
    · obtain ⟨t,hts,ht⟩ := ht
      have T := M.sign w t ht
      by_cases hj : Nonempty (Positions w)
      · obtain ⟨j⟩ := hj
        have hjs : (some j.val : Option I) ≠ some s := by
          intro h; have e := Option.some.inj h; have f := j.property; rw [e,hs] at f; contradiction
        have hjt : (some j.val : Option I) ≠ some t := by
          intro h; have e := Option.some.inj h; have f := j.property; rw [e,ht] at f; contradiction
        letI : Subsingleton (CubicCocycles.HOne (M.action w)) :=
          CubicCocycles.subsingleton_of_two_signs M.loops S T (by simpa using hts.symm) hjs hjt
            (fixed_standard M w j)
        simpa [meridianDim, FiniteDimensional.finrank_zero_of_subsingleton] using (cap_nonneg w)
      · by_cases hr : ∃ r, r ≠ s ∧ r ≠ t ∧ w r = 1
        · obtain ⟨r,hrs,hrt,hr⟩ := hr
          letI : Subsingleton (CubicCocycles.HOne (M.action w)) :=
            CubicCocycles.subsingleton_of_three_signs M.loops S T (M.sign w r hr)
              (by simpa using hts.symm) (by simpa using hrs) (by simpa using hrt)
          simpa [meridianDim, FiniteDimensional.finrank_zero_of_subsingleton] using (cap_nonneg w)
        · have wpair : w = signPair {s,t} := by
            funext i
            by_cases a : i = s
            · subst i; simp [signPair,hs]
            by_cases b : i = t
            · subst i; simp [signPair,ht]
            have h1 : w i ≠ 1 := fun e => hr ⟨i,a,b,e⟩
            have h2 : w i ≠ 2 := fun e => hj ⟨⟨i,e⟩⟩
            have hz : w i = 0 := by generalize w i = v at *; fin_cases v <;> simp_all
            simp [signPair,a,b,hz]
          have terms : (1:ℝ) ≤ ∑ t' ∈ (univ : Finset I).powersetCard 2,
              if w = signPair t' then 1 else 0 := by
            have hm : ({s,t} : Finset I) ∈ (univ : Finset I).powersetCard 2 := by
              simp [mem_powersetCard,hts.symm]
            have b := single_le_sum (f := fun t' => if w = signPair t' then (1:ℝ) else 0)
              (fun _ _ => by positivity) hm
            simpa only [if_pos wpair] using b
          haveI : IsEmpty (Positions w) := ⟨fun j => hj ⟨j⟩⟩
          have dim := LinearMap.finrank_le_finrank_of_injective
            (CubicCocycles.signMap_injective M.loops S)
          have d : meridianDim M w ≤ 1 := by
            simpa [meridianDim,Coordinates,FiniteDimensional.finrank_fintype_fun_eq_card,
              Fintype.card_fun] using dim
          have d' : (meridianDim M w : ℝ) ≤ 1 := by exact_mod_cast d
          unfold bettiCap
          linarith only [d', terms, show 0 ≤ (if w ∈ (unsignedWords I).erase 0 then
            6*(Fintype.card I : ℝ)+2 else 0) by positivity,
            show 0 ≤ ∑ i, (if w ∈ oneSign i then (2:ℝ) else 0) by positivity]
    · let idx : Positions w ↪ Option I :=
        ⟨fun j => some j.val, fun _ _ h => Subtype.ext (Option.some.inj h)⟩
      have away (j : Positions w) : idx j ≠ some s := by
        intro h; have e := Option.some.inj h; have f := j.property; rw [e,hs] at f; contradiction
      have d := CubicCocycles.one_sign_finrank_le_two M.loops (M.action w) S idx away
        (M.xrow w) (M.yrow w)
      have d' : (meridianDim M w : ℝ) ≤ 2 := by exact_mod_cast d
      have hm : w ∈ oneSign s := by
        apply Fintype.mem_piFinset.mpr
        intro j
        by_cases e : j = s
        · subst j; simp [hs]
        · have h1 : w j ≠ 1 := fun h => ht ⟨j,e,h⟩
          simp only [if_neg e,mem_insert,mem_singleton]
          generalize w j = v at *
          fin_cases v <;> simp_all
      have terms := single_le_sum (f := fun i => if w ∈ oneSign i then (2:ℝ) else 0)
        (fun _ _ => by positivity) (mem_univ s)
      dsimp only at terms
      rw [if_pos hm] at terms
      unfold bettiCap
      linarith only [d', terms, show 0 ≤ (if w ∈ (unsignedWords I).erase 0 then
        6*(Fintype.card I : ℝ)+2 else 0) by positivity,
        show 0 ≤ ∑ t ∈ (univ : Finset I).powersetCard 2,
          (if w = signPair t then (1:ℝ) else 0) by positivity]
  · push_neg at hs
    have hm : w ∈ (unsignedWords I).erase 0 := by
      apply mem_erase.mpr
      refine ⟨(mem_erase.mp hw).1,Fintype.mem_piFinset.mpr ?_⟩
      intro i
      have h := hs i
      simp only [mem_insert,mem_singleton]
      generalize w i = v at *
      fin_cases v <;> simp_all
    unfold bettiCap
    rw [if_pos hm]
    obtain ⟨j,hj⟩ : ∃ j, w j = 2 := by
      by_contra! h
      apply (Finset.mem_erase.mp hw).1
      funext i
      have h1 := hs i
      have h2 := h i
      change w i = 0
      generalize w i = a at *
      fin_cases a <;> simp_all
    let idx : Positions w ↪ I := Function.Embedding.subtype _
    have rows : CubicUnsigned.TensorRows M.loops (M.action w) idx :=
      ⟨M.xrow w,M.yrow w,M.xlocal w,M.ylocal w⟩
    have dim := CubicUnsigned.finrank_le M.loops rows ⟨j,hj⟩
    have dn : meridianDim M w ≤ 6 * Fintype.card I + 2 := by unfold meridianDim; omega
    have dr : (meridianDim M w : ℝ) ≤ 6 * Fintype.card I + 2 := by exact_mod_cast dn
    exact dr.trans (by
      have a : 0 ≤ ∑ i, (if w ∈ oneSign i then (2:ℝ) else 0) := by positivity
      have b : 0 ≤ ∑ t ∈ (univ : Finset I).powersetCard 2,
        (if w = signPair t then (1:ℝ) else 0) := by positivity
      linarith)

/-- Every nontrivial tensor with a sign coordinate satisfies its first-cohomology
bound directly from the meridian action. This also covers the pure two-sign
exception, whose coefficient space is one-dimensional. -/
theorem signed_meridian_bound (M : MeridianModel I G) (w : Word I)
    (hw : w ∈ nontrivialWords I) (_signed : ∃ i, w i = 1) :
    (meridianDim M w : ℝ) ≤ bettiCap w := by
  exact meridian_bound M w hw

end TensorTypes
/-- Eigenvalues are counted with algebraic multiplicity, after a complex embedding.
The independent meridian model supplies a genuine crossed-cocycle quotient
in characteristic zero for geometric comparison. -/
structure SurfaceSpectrum (I : Type*) where
  LoopGroup : Type
  [loopGroupInstance : Group LoopGroup]
  meridians : MeridianModel I LoopGroup
  group : Subgroup (I → CubicMonodromy.SymThree)
  eigenvalues : Word I → Fin 5 → List ℂ

attribute [instance] SurfaceSpectrum.loopGroupInstance

/-- Numerical realizations of the individual geometric inputs for §15. Each
identity concerns one tensor character. The dimension and tensor multiplicities
in the resulting error bound are derived from these geometric data. -/
structure SurfaceLaws (S : Finset F) (H : SurfaceSpectrum S) : Prop where
  traceFormula : ∀ w ∈ nontrivialWords S,
    characterSum (points S) (fun p (i : S) => rootCount p (i : F)) w =
      realTrace (H.eigenvalues w 0) - realTrace (H.eigenvalues w 1) +
      realTrace (H.eigenvalues w 2) - realTrace (H.eigenvalues w 3) +
      realTrace (H.eigenvalues w 4)
  affineVanishing : ∀ w ∈ nontrivialWords S,
    H.eigenvalues w 0 = [] ∧ H.eigenvalues w 1 = []
  transitive : CubicMonodromy.transitiveFactors H.group
  isolatedInertia : CubicMonodromy.supportedInertia H.group
  topDuality : ∀ w ∈ nontrivialWords S,
    CubicMonodromy.topMultiplicity H.group w (H.eigenvalues w 4).length
  tameEuler : ∀ w ∈ nontrivialWords S,
    ((H.eigenvalues w 0).length : ℝ) - (H.eigenvalues w 1).length +
      (H.eigenvalues w 2).length - (H.eigenvalues w 3).length +
      (H.eigenvalues w 4).length = rank w * ((1 - (S.card : ℝ)) ^ 2 - (1 - S.card))
  comparisonDuality : ∀ w ∈ nontrivialWords S, (H.eigenvalues w 3).length = meridianDim H.meridians w
  weightTwo : ∀ w ∈ nontrivialWords S, ∀ z ∈ H.eigenvalues w 2, Complex.abs z ≤ Fintype.card F
  weightThree : ∀ w ∈ nontrivialWords S, ∀ z ∈ H.eigenvalues w 3,
    Complex.abs z ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F)

/-- Weight two contributes one factor q per eigenvalue. Weight three contributes
q√q. Tame Euler characteristic fixes the dimension in weight two. -/
theorem character_bound (S : Finset F) (H : SurfaceSpectrum S) (law : SurfaceLaws S H)
    (w : Word S) (hw : w ∈ nontrivialWords S) :
    |characterSum (points S) (fun p (i : S) => rootCount p (i : F)) w| ≤
    rank w * ((S.card:ℝ) * (S.card - 1)) * (Fintype.card F : ℝ) +
      bettiCap w * ((Fintype.card F : ℝ) + (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F)) := by
  have h0 := (law.affineVanishing w hw).1
  have h1 := (law.affineVanishing w hw).2
  have h4 : H.eigenvalues w 4 = [] := List.length_eq_zero.mp
    (CubicMonodromy.top_eq_zero H.group (CubicMonodromy.full_of_inertia _ law.transitive law.isolatedInertia) hw (law.topDuality w hw))
  have he := law.tameEuler w hw
  have ht := law.traceFormula w hw
  simp only [h0,h1,h4,List.length_nil,Nat.cast_zero,zero_sub,neg_zero,zero_add,add_zero] at he
  have hnil : realTrace [] = 0 := rfl
  simp only [h0,h1,h4,hnil,sub_self,zero_add,add_zero] at ht
  have hd : ((H.eigenvalues w 2).length : ℝ) =
      rank w * ((S.card:ℝ) * (S.card - 1)) + (H.eigenvalues w 3).length := by
    linarith only [he, show (1 - (S.card:ℝ))^2 - (1 - S.card) = S.card * (S.card - 1 : ℝ) by ring]
  have hb : ((H.eigenvalues w 3).length : ℝ) ≤ bettiCap w := by
    rw [law.comparisonDuality w hw]
    exact meridian_bound H.meridians w hw
  rw [ht]
  calc
    _ ≤ |realTrace (H.eigenvalues w 2)| + |realTrace (H.eigenvalues w 3)| := abs_sub _ _
    _ ≤ _ := add_le_add (abs_realTrace_le _ _ (law.weightTwo w hw))
      (abs_realTrace_le _ _ (law.weightThree w hw))
    _ ≤ _ := by
      rw [hd]
      nlinarith only [mul_le_mul_of_nonneg_right hb (show (0:ℝ) ≤ Fintype.card F by positivity),
        mul_le_mul_of_nonneg_right hb
          (show 0 ≤ (Fintype.card F : ℝ) * Real.sqrt (Fintype.card F) by positivity)]

/-- Equation (12.1), on the actual finite-field escape count, from the
per-character geometric laws. All sums over growing sets are explicit. -/
theorem trace_deviation_of_spectra (S : Finset F) (H : SurfaceSpectrum S) (law : SurfaceLaws S H) :
    CubicAsymptotics.traceDeviation (Fintype.card F) S.card (escapeCount S) := by
  classical
  let q : ℝ := Fintype.card F
  let ell : ℝ := S.card
  let A := nontrivialWords S
  let Z (w : Word S) := characterSum (points S) (fun p (i : S) => rootCount p (i : F)) w
  have hc := centered_count (points S) (fun p (i : S) => rootCount p (i : F))
  rw [escape_as_filter,card_points] at hc
  simp only [Fintype.card_coe] at hc
  unfold CubicAsymptotics.traceDeviation
  rw [show escapeCount S = (escapePairs S).card from rfl, hc]
  have bs : ∑ w ∈ A, bettiCap w ≤ CubicAsymptotics.highWeight S.card := by
    have e := sum_bettiCap (I := S)
    simp only [Fintype.card_coe] at e
    rw [← e]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun w _ _ => cap_nonneg w)
  have rs : ∑ w ∈ A, rank w = 4 ^ S.card - 1 := by
    simpa [A] using sum_nontrivial_ranks (I := S)
  calc
    |∑ w ∈ A, coefficient w * Z w| ≤ ∑ w ∈ A, |coefficient w * Z w| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ A, (rank w * (ell * (ell - 1)) * q + bettiCap w * (q + q * Real.sqrt q)) := by
      apply sum_le_sum
      intro w hw
      rw [abs_mul, abs_coefficient, one_mul]
      exact character_bound S H law w hw
    _ ≤ _ := by
      rw [sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul, rs]
      have h := mul_le_mul_of_nonneg_right bs (show 0 ≤ q + q * Real.sqrt q by dsimp [q]; positivity)
      dsimp [q,ell] at *
      linarith only [h]

theorem blocking_card_lower_of_spectra (S : Finset F) (h2 : (2:F) ≠ 0)
    (hq : Fintype.card F % 3 = 2) (hlarge : 16 ≤ (Fintype.card F : ℝ))
    (H : SurfaceSpectrum S) (law : SurfaceLaws S H) (hs : ProjectiveBlocks 3 (S : Set F)) :
    (Real.log (Fintype.card F) - 2 * Real.log (Real.log (Fintype.card F))) / Real.log 4 - 5 <
      (S.card : ℝ) :=
  blocking_card_lower_of_trace S h2 hq hlarge (trace_deviation_of_spectra S H law) hs

end BlockingCurves.CubicSurfaceTrace
