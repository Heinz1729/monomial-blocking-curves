import CubicAlteration

/-! Two incidence counts for the cubic pencil. The common hits of specified lines and
the common misses of specified translates are different incidence problems. -/
namespace BlockingCurves.CubicDoubleMiss

open Finset CubicValueSet CubicCovering Polynomial
variable {F : Type*} [Field F] [Fintype F]

noncomputable section
open Classical
local instance : DecidableEq F := Classical.decEq _

/-- For any two lines, at least (q-2)/3 parameters hit both. -/
theorem common_hits_bound (m b n c : F) (hq : Fintype.card F % 3 = 2) :
    Fintype.card F ≤ 3 * ((missedParameters m b ∪ missedParameters n c)ᶜ).card + 2 := by
  have h₁ := line_miss_bound m b hq
  have h₂ := line_miss_bound n c hq
  have hu := card_union_le (missedParameters m b) (missedParameters n c)
  have hl := card_le_univ (missedParameters m b ∪ missedParameters n c)
  rw [card_compl]
  omega

/-- In every field of the permutation family with q>2, any two nonhorizontal
lines can be repaired by one translate, with no curve or place estimates. -/
theorem commonHit_two (hq : Fintype.card F % 3 = 2) (hq2 : 2 < Fintype.card F) :
    CubicAlteration.CommonHit F 2 := by
  classical
  intro R hR
  by_cases h₂ : R.card = 2
  · obtain ⟨l,n,_,rfl⟩ := card_eq_two.mp h₂
    let S := (missedParameters (l.1:F) l.2 ∪ missedParameters (n.1:F) n.2)ᶜ
    have hb := common_hits_bound (l.1:F) l.2 (n.1:F) n.2 hq
    have hs : 0 < S.card := by change _ ≤ 3*S.card+2 at hb; omega
    obtain ⟨a,ha⟩ := card_pos.mp hs
    have hh : CubicAlteration.Hits a l ∧ CubicAlteration.Hits a n := by
      simpa [S,missedParameters,CubicAlteration.Hits,not_or] using ha
    exact ⟨a,by simpa using hh⟩
  · obtain ⟨l,hl⟩ := card_le_one_iff_subset_singleton.mp (show R.card ≤ 1 by omega)
    refine ⟨-l.2,fun n hn => ?_⟩
    have e : n = l := mem_singleton.mp (hl hn)
    subst n
    exact ⟨0, by simp⟩

private theorem conic_card_exact (m : F) (hm : m ≠ 0) (hq : Fintype.card F % 3 = 2) :
    (conic m).card = Fintype.card F + 1 := by
  classical
  have hzero : conic (0 : F) = {(0,0)} := by
    ext ⟨x,y⟩
    simp only [conic, mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq, normForm]
    constructor
    · intro h
      by_cases hx : x = 0
      · subst x
        have : y^2 = 0 := by simpa using h
        exact ⟨rfl, pow_eq_zero this⟩
      · exfalso
        apply unit_form_ne hq (y/x)
        field_simp
        linear_combination x*h
    · rintro ⟨rfl,rfl⟩
      simp
  let Q := Fintype.card F
  have ht : ∑ a : F, (conic a).card = Q*Q := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (F × F))) (t := univ)
      (f := fun p => normForm p.1 p.2) (fun _ _ => mem_univ _)
    simpa [conic,Q] using hh.symm
  let A := (univ : Finset F).erase 0
  have hA : A.card + 1 = Q := by
    simpa only [A,Q] using card_erase_add_one (s := (univ : Finset F)) (mem_univ (0:F)) |>.trans card_univ
  have hE : ∑ a ∈ A, (conic a).card + 1 = Q*Q := by
    have h := sum_erase_add (s := (univ : Finset F)) (fun a => (conic a).card) (mem_univ (0:F))
    simpa only [← ht, hzero, card_singleton, A] using h
  have hall := sum_eq_sum_iff_of_le (s := A)
    (f := fun a => (conic a).card) (g := fun _ => Q+1) (fun a _ => conic_card_le a hq)
  apply hall.mp _ m (mem_erase.mpr ⟨hm,mem_univ _⟩)
  rw [sum_const, Nat.nsmul_eq_mul]
  nlinarith only [hE, hA, congrArg (fun x => x*Q) hA]

private theorem roots_le_three (m b a : F) : (rootsAt m b a).card ≤ 3 := by
  classical
  let P : F[X] := X^3 - (C m * X + C (b+a))
  have hdeg : P.natDegree = 3 := by
    have hl : (C m * X + C (b+a)).natDegree ≤ 1 := by
      apply (natDegree_add_le _ _).trans
      apply max_le
      · exact (natDegree_mul_le (p := C m) (q := X)).trans (by simp)
      · simp
    dsimp only [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    rw [natDegree_X_pow]
    omega
  have hp : P ≠ 0 := by intro h; simp [h] at hdeg
  have hs : rootsAt m b a ⊆ P.roots.toFinset := by
    intro x hx
    obtain ⟨_,hx⟩ := mem_filter.mp hx
    rw [Multiset.mem_toFinset, mem_roots hp]
    dsimp [IsRoot, P]
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    dsimp [cubic] at hx
    linear_combination hx
  exact ((card_le_card hs).trans P.roots.toFinset_card_le).trans ((card_roots' P).trans hdeg.le)

private theorem fibre_exact (m b a : F) (hm : m ≠ 0) :
    3*(rootsAt m b a).card + (if (rootsAt m b a).card = 0 then 3 else 0) =
      3 + (pairsAt m b a).card := by
  apply Nat.le_antisymm (fibre_budget m b a)
  let R := rootsAt m b a
  let P := pairsAt m b a
  change 3 + P.card ≤ 3*R.card + _
  have hr (x : F) : x ∈ R ↔ cubic m b x = a := by simp [R,rootsAt]
  have hp {x y : F} (h : (x,y) ∈ P) : x ∈ R ∧ y ∈ R ∧ normForm x y = m := by
    have hn := (mem_filter.mp (mem_filter.mp h).1).2
    have hx := (mem_filter.mp h).2
    change normForm x y = m at hn
    change cubic m b x = a at hx
    refine ⟨(hr x).2 hx, (hr y).2 ?_, hn⟩
    rw [← hx]
    dsimp [cubic, normForm] at hn ⊢
    linear_combination (y-x)*hn
  by_cases hd : ∃ t : F, (t,t) ∈ P
  · obtain ⟨t,ht⟩ := hd
    obtain ⟨htR,_,hm'⟩ := hp ht
    have h0 : 3*t ≠ 0 := by
      intro h
      apply hm
      dsimp [normForm] at hm'
      linear_combination -hm' + t*h
    have hne : t ≠ -2*t := by intro e; apply h0; linear_combination e
    have hR : R = {t,-2*t} := by
      ext u
      rw [hr, mem_insert, mem_singleton]
      have hval := (hr t).mp htR
      constructor
      · intro hu
        have hsplit : (u-t)^2*(u+2*t)=0 := by
          dsimp [cubic, normForm] at hu hval hm'
          linear_combination hu - hval - (u-t)*hm'
        rcases mul_eq_zero.mp hsplit with h | h
        · exact Or.inl (sub_eq_zero.mp (pow_eq_zero h))
        · right; linear_combination h
      · rintro (rfl|rfl)
        · exact hval
        · dsimp [cubic,normForm] at hval hm' ⊢
          linear_combination hval - 3*t*hm'
    have hP : P ⊆ R.offDiag ∪ {(t,t)} := by
      rintro ⟨x,y⟩ hxy
      obtain ⟨hx,hy,hn⟩ := hp hxy
      by_cases h : x = y
      · subst y
        have hx' : x = t ∨ x = -2*t := by simpa only [hR,mem_insert,mem_singleton] using hx
        rcases hx' with rfl|rfl
        · simp
        · exfalso
          apply h0
          apply pow_eq_zero (n := 2)
          dsimp [normForm] at hn hm'
          linear_combination hn-hm'
      · exact mem_union_left _ (mem_offDiag.mpr ⟨hx,hy,h⟩)
    have hc := (card_le_card hP).trans (card_union_le _ _)
    have hcard : R.card = 2 := by rw [hR,card_pair hne]
    rw [offDiag_card, hcard, card_singleton] at hc
    change 3 + P.card ≤ 3*R.card + (if R.card = 0 then 3 else 0)
    rw [hcard]
    omega
  · have hP : P ⊆ R.offDiag := by
      rintro ⟨x,y⟩ h
      obtain ⟨hx,hy,_⟩ := hp h
      refine mem_offDiag.mpr ⟨hx,hy,?_⟩
      intro e
      change x = y at e
      subst y
      exact hd ⟨x,h⟩
    have hc := card_le_card hP
    rw [offDiag_card] at hc
    have h3 := roots_le_three m b a
    have h4 : R.card = 0 ∨ R.card = 1 ∨ R.card = 2 ∨ R.card = 3 := by
      change R.card ≤ 3 at h3
      omega
    change 3 + P.card ≤ 3*R.card + (if R.card = 0 then 3 else 0)
    rcases h4 with h|h|h|h <;> rw [h] at hc ⊢ <;> norm_num at hc ⊢ <;> first | exact hc | omega

/-- For each nonzero slope, including in characteristic two, the missing set has
exactly (q+1)/3 parameters. -/
theorem line_miss_exact {m : F} (b : F) (hm : m ≠ 0) (hq : Fintype.card F % 3 = 2) :
    3*(missedParameters m b).card = Fintype.card F + 1 := by
  classical
  have hroots : Fintype.card F = ∑ a : F, (rootsAt m b a).card := by
    simpa [rootsAt] using card_eq_sum_card_fiberwise
      (f := cubic m b) (s := univ) (t := univ) (fun _ _ => mem_univ _)
  have hpairs : (conic m).card = ∑ a : F, (pairsAt m b a).card :=
    card_eq_sum_card_fiberwise (f := fun p : F × F => cubic m b p.1) (fun _ _ => mem_univ _)
  have hs := sum_congr (rfl : (univ : Finset F) = univ) (fun a _ => fibre_exact m b a hm)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← hroots, ← hpairs] at hs
  have he (a : F) : (rootsAt m b a).card = 0 ↔ ¬ ∃ x : F, x^3-m*x-b = a := by
    simp [card_eq_zero,rootsAt,filter_eq_empty_iff,cubic]
  simp_rw [he] at hs
  rw [← sum_filter] at hs
  simp only [sum_const,nsmul_eq_mul,card_univ,Nat.cast_id,conic_card_exact m hm hq] at hs
  rw [Nat.mul_comm (Fintype.card F) 3] at hs
  have h := Nat.add_left_cancel hs
  rw [← h, Nat.mul_comm]
  congr 2

private theorem line_card (m b : F) (hm : m ≠ 0) (hq : Fintype.card F % 3 = 2) :
    (missedParameters m b).card = (Fintype.card F+1)/3 := by
  have he := line_miss_exact b hm hq
  omega

private theorem intercept_card (m a : F) :
    (univ.filter fun c : F => a ∈ missedParameters m c).card =
      (missedParameters m 0).card := by
  apply card_bijective (Equiv.addRight a) (Equiv.addRight a).bijective
  intro b
  simp only [mem_filter,mem_univ,true_and,missedParameters,sub_zero]
  change (¬ ∃ x : F, x^3-m*x-b=a) ↔ (¬ ∃ x : F, x^3-m*x=b+a)
  apply not_congr
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x, by linear_combination hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨x, by linear_combination hx⟩

/-- Move the second intercept through the field, keeping both nonzero slopes fixed.
The total number of pairs (intercept, parameter missing both lines) is exactly h². -/
theorem double_miss_sum {m n : F} (b : F) (hm : m ≠ 0) (hn : n ≠ 0)
    (hq : Fintype.card F % 3 = 2) :
    ∑ c : F, (missedParameters m b ∩ missedParameters n c).card = ((Fintype.card F+1)/3)^2 := by
  classical
  let S := missedParameters m b
  let h := (Fintype.card F+1)/3
  have hf (c : F) : missedParameters m b ∩ missedParameters n c =
      S.filter fun a => a ∈ missedParameters n c := by
    ext a; simp [S]
  have hi (a : F) : (univ.filter fun c : F => a ∈ missedParameters n c).card = h := by
    rw [intercept_card, line_card _ _ hn hq]
  have hc := line_card m b hm hq
  calc
    _ = ∑ c : F, ∑ a ∈ S, if a ∈ missedParameters n c then 1 else 0 := by
      apply sum_congr rfl
      intro c _
      rw [hf, card_eq_sum_ones, sum_filter]
    _ = ∑ a ∈ S, ∑ c : F, if a ∈ missedParameters n c then 1 else 0 := sum_comm
    _ = ∑ _a ∈ S, h := by
      apply sum_congr rfl
      intro a _
      simpa only [sum_boole] using hi a
    _ = _ := by simp [S, h, hc, pow_two]

/-- For distinct parallel lines, removing the identical line from the preceding
sum subtracts exactly h: the mean intersection is h(h−1)/(q−1). -/
theorem parallel_double_miss_sum {m : F} (b : F) (hm : m ≠ 0)
    (hq : Fintype.card F % 3 = 2) :
    ∑ c ∈ (univ.erase b), (missedParameters m b ∩ missedParameters m c).card =
      ((Fintype.card F+1)/3)*((Fintype.card F+1)/3-1) := by
  classical
  have ht := sum_erase_add (s := (univ : Finset F))
    (fun c => (missedParameters m b ∩ missedParameters m c).card) (mem_univ b)
  dsimp only at ht
  rw [double_miss_sum b hm hm hq, inter_self, line_card m b hm hq, pow_two] at ht
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  omega

/-- Nonhorizontal lines avoiding the translates with parameters a and c. -/
def missedLines (a c : F) : Finset (Fˣ × F) :=
  univ.filter fun l => a ∈ missedParameters (l.1 : F) l.2 ∧ c ∈ missedParameters (l.1 : F) l.2

private theorem change_miss (u : Fˣ) (v m b a : F) :
    (u:F)^3*a+v ∈ missedParameters ((u:F)^2*m) ((u:F)^3*b-v) ↔
      a ∈ missedParameters m b := by
  simp only [missedParameters,mem_filter,mem_univ,true_and]
  apply not_congr
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z/(u:F), ?_⟩
    field_simp [u.ne_zero]
    linear_combination (u:F)*hz
  · rintro ⟨x,hx⟩
    exact ⟨(u:F)*x, by linear_combination (u:F)^3*hx⟩

private def changeLine (u : Fˣ) (v : F) : (Fˣ × F) ≃ (Fˣ × F) where
  toFun l := (u^2*l.1,(u:F)^3*l.2-v)
  invFun l := ((u^2)⁻¹*l.1,(l.2+v)/(u:F)^3)
  left_inv l := Prod.ext (by simp) (by simp [u.ne_zero])
  right_inv l := Prod.ext (by simp) (by field_simp)

/-- The affine action on parameters is doubly transitive when cubing is bijective. -/
private theorem pair_count_uniform {a c z t : F} (ha : a ≠ c) (hz : z ≠ t)
    (hq : Fintype.card F % 3 = 2) : (missedLines a c).card = (missedLines z t).card := by
  obtain ⟨w,hw⟩ := CubicSlope.cube_surjective hq ((t-z)/(c-a))
  have hd : c-a ≠ 0 := sub_ne_zero.mpr ha.symm
  have h₀ : w ≠ 0 := by
    intro h
    rw [h] at hw
    have : (t-z)/(c-a) = 0 := by simpa using hw.symm
    exact (div_ne_zero (sub_ne_zero.mpr hz.symm) hd) this
  let u := Units.mk0 w h₀
  let v := z-(u:F)^3*a
  have hm : (u:F)^3*(c-a)=t-z := (eq_div_iff hd).mp hw
  have h₁ : (u:F)^3*a+v = z := by dsimp [v]; ring
  have h₂ : (u:F)^3*c+v = t := by dsimp [v]; linear_combination hm
  apply card_bijective (changeLine u v) (changeLine u v).bijective
  rintro ⟨m,b⟩
  simp only [missedLines,mem_filter,mem_univ,true_and]
  change _ ↔ z ∈ missedParameters ((u:F)^2*(m:F)) ((u:F)^3*b-v) ∧
    t ∈ missedParameters ((u:F)^2*(m:F)) ((u:F)^3*b-v)
  rw [← h₁, ← h₂, change_miss, change_miss]

/-- For two distinct translates the number of lines missing both is h(h-1),
with h=(q+1)/3, after summing over all nonzero slopes. Horizontal lines hit
every translate because cubing is onto. -/
theorem pair_miss_exact {a c : F} (ha : a ≠ c) (hq : Fintype.card F % 3 = 2) :
    (missedLines a c).card = ((Fintype.card F+1)/3)*((Fintype.card F+1)/3-1) := by
  classical
  let A := (univ : Finset F).offDiag
  let L := (univ : Finset (Fˣ × F))
  let h := (Fintype.card F+1)/3
  let R (p : F × F) (l : Fˣ × F) := p.1 ∈ missedParameters (l.1:F) l.2 ∧
    p.2 ∈ missedParameters (l.1:F) l.2
  have hleft (p : F × F) (hp : p ∈ A) : (L.filter (R p)).card = (missedLines a c).card := by
    have eq : L.filter (R p) = missedLines p.1 p.2 := by
      ext l; simp [L,R,missedLines]
    rw [eq]
    exact pair_count_uniform (mem_offDiag.mp hp).2.2 ha hq
  have hright (l : Fˣ × F) (_ : l ∈ L) : (A.filter (fun p => R p l)).card = h*(h-1) := by
    have eq : A.filter (fun p => R p l) = (missedParameters (l.1:F) l.2).offDiag := by
      ext p
      simp [A,R,mem_offDiag,and_assoc,and_comm,and_left_comm]
    have he := line_miss_exact l.2 l.1.ne_zero hq
    have hc : (missedParameters (l.1:F) l.2).card = h := by dsimp [h]; omega
    rw [eq, offDiag_card, hc, Nat.mul_sub_left_distrib, Nat.mul_one]
  have hc : A.card = L.card := by
    simp [A,L,offDiag_card,Fintype.card_units, Nat.mul_comm,Nat.mul_sub_left_distrib]
  have hedges : (∑ p ∈ A, (L.filter (R p)).card) =
      ∑ l ∈ L, (A.filter (fun p => R p l)).card := by
    simp_rw [card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hd : A.card*(missedLines a c).card = L.card*(h*(h-1)) := by
    rw [sum_eq_card_nsmul hleft, sum_eq_card_nsmul hright] at hedges
    exact hedges
  rw [hc] at hd
  exact Nat.mul_left_cancel (by simp [L, Fintype.card_pos]) hd

end
end BlockingCurves.CubicDoubleMiss
