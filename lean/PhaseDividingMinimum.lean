import PhaseDividingUpper
import PhaseBlockCover
import PhasePointCover
import PhaseTraceLower

/-! Putting the affine-block estimate into the monomial pencil. The kernel
of the cyclotomic character supplies its linear Frobenius branch. -/
namespace BlockingCurves.PhaseDividing
open Finset PhaseDirection

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private theorem empty_le_of_translate (G V : Finset E) (b : E)
    (sub : ∀ x ∈ G, x-b ∈ V) :
    emptyCount (fun p : E × E => hits F V p.1 p.2) ≤
      emptyCount (fun p : E × E => hits F G p.1 p.2) := by
  classical
  let P := univ.filter (fun p : E × E => hits F V p.1 p.2 = 0)
  let Q := univ.filter (fun p : E × E => hits F G p.1 p.2 = 0)
  let move (p:P) : Q := ⟨(p.val.1, p.val.2+b), by
    refine Finset.mem_filter.mpr ⟨mem_univ _,(hits_eq_zero_iff _ _ _).mpr ?_⟩
    intro t ht
    have hm := ((hits_eq_zero_iff _ _ _).mp (Finset.mem_filter.mp p.property).2) t
    apply hm
    have eq : point t (p.val.1,p.val.2+b)-b = point t p.val := by dsimp [point]; ring
    exact eq ▸ sub _ ht⟩
  have hi : Function.Injective move := by
    intro u v h
    have h₁ : u.val.1 = v.val.1 := congrArg (fun (z:Q) => z.val.1) h
    have h₂ : u.val.2 + b = v.val.2 + b := congrArg (fun (z:Q) => z.val.2) h
    exact Subtype.ext (Prod.ext h₁ (add_right_cancel h₂))
  have h := Fintype.card_le_of_injective move hi
  simpa only [Fintype.card_coe] using h

private theorem actual_branch_group {m n : ℕ} (d : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) :
    ∃ H : Subgroup Eˣ, H.index = m ∧
      m * (carrier H).card + 1 = Fintype.card E ∧
      ∀ x ∈ carrier H, x ^ ((Fintype.card E-1)/m) = 1 := by
  classical
  let k := (Fintype.card E-1)/m
  have dq : m ∣ Fintype.card E-1 := by
    rw [size,← NormPencil.normExponent_mul (Fintype.card F) n (by exact Fintype.card_pos),
      Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right d _
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  let H := Subgroup.zpowers (g^m)
  letI : Nonempty H := ⟨1⟩
  have hc : Fintype.card H = k := by
    dsimp [H,k]
    rw [Fintype.card_zpowers,orderOf_pow g,orderOf_eq_card_of_forall_mem_zpowers hg,
      Fintype.card_units,Nat.gcd_eq_right dq]
  have hcard := carrier_card H
  have hprod : m * Fintype.card H = Fintype.card E-1 := by
    rw [hc,Nat.mul_comm]; exact Nat.div_mul_cancel dq
  have hi : H.index=m := Nat.eq_of_mul_eq_mul_right Fintype.card_pos
    ((H.index_mul_card.trans (Fintype.card_units (α := E))).trans hprod.symm)
  refine ⟨H,hi,?_,?_⟩
  · rw [hcard,hprod,Nat.sub_add_cancel Fintype.card_pos]
  · intro x hx
    obtain ⟨u,_,rfl⟩ := mem_image.mp hx
    have hu : u^k = 1 := hc ▸ pow_card_eq_one
    exact congrArg (fun z:H => ((z.val:Eˣ):E)) hu

private theorem rate {s q m c : ℕ} (hs : 0 < s) (hq : 1 < q) (hm : 0 < m)
    (hc : m*c+1=q) :
    1/(s:ℝ)+(m:ℝ)/(s*(c/(q:ℝ))) ≤ (1+2*(m:ℝ)^2)/s := by
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have cpos : 0 < c := by by_contra! he; simp [Nat.eq_zero_of_le_zero he] at hc; omega
  have hc' : (0:ℝ) < c := by exact_mod_cast cpos
  have hmc : (m:ℝ)*c+1=q := by exact_mod_cast hc
  have one : (1:ℝ) ≤ (m:ℝ)*c := by exact_mod_cast Nat.mul_pos hm cpos
  have h := mul_le_mul_of_nonneg_left (show (q:ℝ) ≤ 2*m*c by linarith) hm'.le
  have hcE : (m:ℝ)/(s*(c/(q:ℝ))) = (m*q/c)/s := by field_simp; ring
  rw [hcE,add_div]
  apply add_le_add_left
  apply div_le_div_of_nonneg_right _ hs'.le
  apply (div_le_iff hc').2
  nlinarith only [h]

/-- Single-block failure for every actual slope and intercept. No restriction
on the relative degree is required for this upper bound. -/
theorem cyclotomic_block_bound {m n : ℕ} (hm : 2 ≤ m) (d : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) (a b:E) :
    let k := (Fintype.card E-1)/m
    (emptyCount (fun p:E×E => hits F (valueSet (Fintype.card F+k) a b) p.1 p.2):ℝ) /
      (Fintype.card E:ℝ)^2 ≤ (1+2*(m:ℝ)^2)/Fintype.card F := by
  classical
  obtain ⟨H,hindex,hcard,hunit⟩ := actual_branch_group d size
  let k := (Fintype.card E-1)/m
  let s := Fintype.card F
  let G := (carrier H).image (fun x:E => x^s-a*x)
  let V := valueSet (s+k) a b
  have sub (u:E) (hu : u ∈ G) : u-b ∈ V := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    refine mem_image.mpr ⟨x,mem_univ _,?_⟩
    simp only [pow_add, hunit x hx, mul_one]
  have hmiss := empty_le_of_translate (F := F) G V b sub
  have hbranch := frobenius_block_bound (F := F) H a
  change (emptyCount (fun p:E×E => hits F V p.1 p.2):ℝ)/_ ≤ _
  apply le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr hmiss) (sq_nonneg _))
  apply le_trans hbranch
  rw [hindex]
  exact rate Fintype.card_pos Fintype.one_lt_card (by omega) hcard

/-- On a sufficiently large ground field the cyclotomic Frobenius pencil
admits at most 4n+1 affine lines' worth of translation parameters. -/
theorem large_ground_projective_upper {m n : ℕ} (hm : 2 ≤ m) (d : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) (large : (1+2*m^2)^2 ≤ Fintype.card F) :
    ∃ S : Finset E, ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S:Set E) ∧
      S.card ≤ (4*n+1)*Fintype.card F := by
  have hd : 2 ≤ Fintype.card F+(Fintype.card E-1)/m :=
    le_trans (Fintype.one_lt_card (α := F)) (Nat.le_add_right _ _)
  exact projective_block_sampling hd size (A := 1+2*(m:ℝ)^2)
    (by nlinarith only [sq_nonneg (m:ℝ)]) (by exact_mod_cast large)
    (cyclotomic_block_bound hm d size)

/-- Both sampling ranges with a constant independent of n and of the base
field. The lower bound in the next theorem is the part that needs m ∣ n. -/
theorem uniform_projective_upper {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (d : m ∣ Fintype.card F-1) (size : Fintype.card E = Fintype.card F^n) :
    ∃ S : Finset E, ProjectiveBlocks (Fintype.card F+(Fintype.card E-1)/m) (S : Set E) ∧
      S.card ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  by_cases small : Fintype.card F < (1+2*m^2)^2
  · exact PhasePointCover.small_base_upper hm hn d size small
  obtain ⟨S,hS,hB⟩ := large_ground_projective_upper hm d size (Nat.le_of_not_lt small)
  refine ⟨S,hS,hB.trans (Nat.mul_le_mul_right _ ?_)⟩
  have four : 4 ≤ 2*m*(1+(1+2*m^2)^2) := by
    calc
      4 ≤ 2*m := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
  have haux := Nat.mul_le_mul_right n four
  rw [Nat.add_mul,one_mul]
  omega

/-- The entire divisible side of the dichotomy, at the independent
projective minimum. Both constants are uniform in s and n. -/
theorem divisible_pencil_minimum_bounds {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (d : m ∣ Fintype.card F-1) (phase : m ∣ n) (size : Fintype.card E = Fintype.card F^n) :
    ∃ B : ℕ, AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F+(Fintype.card E-1)/m) B ∧
      1+n*(Fintype.card F-1)/m ≤ B ∧ B ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  classical
  obtain ⟨S,hS,hcard⟩ := uniform_projective_upper hm hn d size
  let D := Fintype.card F+(Fintype.card E-1)/m
  let P := fun r : ℕ => ∃ U : Finset E, U.card=r ∧ ProjectiveBlocks D (U:Set E)
  have feasible : P S.card := ⟨S,rfl,hS⟩
  have ex : ∃ r, P r := ⟨_,feasible⟩
  have hd : 2 ≤ D := (Fintype.one_lt_card (α := F)).trans_le (Nat.le_add_right _ _)
  obtain ⟨U,hU,blocks⟩ := Nat.find_spec ex
  refine ⟨Nat.find ex, (AGY_minimum_iff hd _).2
    ⟨Nat.find_spec ex,fun _ h => Nat.find_min' ex h⟩,?_,(Nat.find_min' ex feasible).trans hcard⟩
  rw [← hU]
  exact PhaseTraceLower.divisible_projective_lower_rounded hm hn d phase size U blocks

end BlockingCurves.PhaseDividing
