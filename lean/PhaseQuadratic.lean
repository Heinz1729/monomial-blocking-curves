import PhaseBranches
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The quadratic twist of relative Frobenius over an odd field.
At slope one its two branches are in the two conjugation eigenspaces.
At every slope any nonzero scalar projection takes all ground-field values. -/

namespace BlockingCurves.PhaseQuadratic

open NormPencil

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private abbrev exponent (F E : Type*) [Fintype F] [Fintype E] :=
  Fintype.card F + (Fintype.card E - 1) / 2

private theorem odd_char {K : Type*} [Field K] [Fintype K] (h : Odd (Fintype.card K)) :
    ringChar K ≠ 2 := by
  intro hc
  have h0 := FiniteField.even_card_of_char_two hc
  have h1 := Nat.odd_iff.1 h
  omega

private theorem branch_formula [DecidableEq E] (oddE : Odd (Fintype.card E))
    (σ : E ≃ₐ[F] E) (hσ : ∀ x : E, σ x = x ^ Fintype.card F) (x : E) :
    x ^ exponent F E = (quadraticChar E x : E) * σ x := by
  rw [exponent, pow_add, hσ, quadraticChar_eq_pow_of_char_ne_two' (odd_char oddE)]
  have h := Nat.odd_iff.1 oddE
  rw [show (Fintype.card E - 1) / 2 = Fintype.card E / 2 by omega, mul_comm]

private theorem scalar_pow (oddF : Odd (Fintype.card F))
    (size : Fintype.card E = Fintype.card F ^ 2) (c : F) :
    (algebraMap F E c) ^ exponent F E = algebraMap F E c := by
  rw [← map_pow]
  apply congrArg
  by_cases hc : c = 0
  · have hp : 0 < exponent F E := Nat.add_pos_left Fintype.card_pos _
    simp [hc, zero_pow hp.ne']
  rw [exponent, pow_add, FiniteField.pow_card]
  obtain ⟨u,hu⟩ := oddF
  have he : (Fintype.card E - 1) / 2 = (Fintype.card F-1)*(u+1) := by
    rw [size, hu]
    have h : (2*u+1)^2 = 2*(2*u*(u+1))+1 := by ring
    rw [h]
    simp
  rw [he, pow_mul, FiniteField.pow_card_sub_one_eq_one _ hc, one_pow, mul_one]

private theorem square_vanish (two : (2 : E) ≠ 0) (L : E →ₗ[F] F)
    (h : ∀ x : E, L (x^2) = 0) (x : E) : L x = 0 := by
  have he : x = ((x+1)/2)^2 - ((x-1)/2)^2 := by field_simp; ring
  rw [he, map_sub, h, h, sub_self]

private theorem projection_nonzero (oddF : Odd (Fintype.card F))
    (oddE : Odd (Fintype.card E)) (σ : E ≃ₐ[F] E)
    (hσ : ∀ x : E, σ x = x ^ Fintype.card F) (π : E →ₗ[F] F)
    (nonzero : π ≠ 0) (a : E) :
    ∃ x : E, π (x ^ exponent F E - a*x) ≠ 0 := by
  classical
  by_contra! hall
  let P := π.comp (σ.toLinearMap - LinearMap.mulLeft F a)
  let M := π.comp (-σ.toLinearMap - LinearMap.mulLeft F a)
  have two : (2:E) ≠ 0 := Ring.two_ne_zero (odd_char oddE)
  have pos : ∀ x : E, P x = 0 := by
    apply square_vanish two P
    intro x
    change π (σ (x ^ 2) - a * x ^ 2) = _
    by_cases hx : x = 0
    · simp [hx]
    have h := hall (x^2)
    simpa only [branch_formula oddE σ hσ, quadraticChar_sq_one' hx, Int.cast_one,
      one_mul] using h
  obtain ⟨z,hz⟩ := quadraticChar_exists_neg_one (odd_char oddE)
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have negsq : ∀ x : E, (M.comp (LinearMap.mulLeft F z)) (x^2) = 0 := by
    intro x
    change π (-σ (z*x^2) - a*(z*x^2)) = _
    by_cases hx : x = 0
    · simp [hx]
    have hz' : quadraticChar E (z*x^2) = -1 := by rw [map_mul, hz, quadraticChar_sq_one' hx, mul_one]
    have h := hall (z*x^2)
    rw [branch_formula oddE σ hσ (z*x^2)] at h
    rw [hz', Int.cast_neg, Int.cast_one, neg_one_mul] at h
    exact h
  have neg (x : E) : M x = 0 := by
    have h := square_vanish two (M.comp (LinearMap.mulLeft F z)) negsq (z⁻¹*x)
    change M (z*(z⁻¹*x)) = 0 at h
    rwa [← mul_assoc, mul_inv_cancel hz0, one_mul] at h
  apply nonzero
  ext x
  obtain ⟨y,rfl⟩ := σ.surjective x
  have hp := pos y
  have hm := neg y
  change π (σ y - a*y) = 0 at hp
  change π (-σ y - a*y) = 0 at hm
  rw [map_sub] at hp
  rw [map_sub, map_neg] at hm
  change π (σ y) = 0
  apply (mul_eq_zero.mp (show (2:F)*π (σ y) = 0 by linear_combination hp - hm)).resolve_left
  exact Ring.two_ne_zero (odd_char oddF)

/-- Every nonzero linear functional gives a blocking hyperplane kernel in the quadratic pencil. -/
theorem projection_blocks (oddF : Odd (Fintype.card F)) (size : Fintype.card E = Fintype.card F ^ 2)
    (π : E →ₗ[F] F) (nonzero : π ≠ 0) :
    GraphHits (fun x : E => x ^ (Fintype.card F + (Fintype.card E-1)/2))
      (LinearMap.ker π : Set E) := by
  intro a b
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have oddE : Odd (Fintype.card E) := size ▸ oddF.pow
  obtain ⟨y,hy⟩ := projection_nonzero oddF oddE σ hσ π nonzero a
  let c := π b / π (y^exponent F E - a*y)
  refine ⟨c • y, ?_⟩
  change π ((c • y)^exponent F E - a*(c • y) - b) = 0
  rw [show (c • y)^exponent F E - a*(c • y) = c • (y^exponent F E - a*y) by
    simp only [Algebra.smul_def, mul_pow, scalar_pow oddF size]; ring,
    map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hy, sub_self]

private theorem missing {K T : Type*} [Fintype K] (S : Finset T)
    (hS : S.card < Fintype.card K) (f : T → T) (g : K → T) (inj : Function.Injective g) :
    ∃ c : K, ∀ u ∈ S, f u ≠ g c := by
  classical
  by_contra! h
  have sub : Finset.univ.image g ⊆ S.image f := by
    intro x hx
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨u,hu,he⟩ := h c
    exact Finset.mem_image.2 ⟨u,hu,he⟩
  have le := (Finset.card_le_card sub).trans Finset.card_image_le
  rw [Finset.card_image_of_injective _ inj, Finset.card_univ] at le
  omega

/-- At slope one the two branches lie on the conjugation eigenspaces. The intercept
can have both signed trace coordinates outside the projections of a short parameter set. -/
theorem cardinal_lower (oddF : Odd (Fintype.card F)) (size : Fintype.card E = Fintype.card F ^ 2)
    (S : Finset E)
    (blocks : GraphHits (fun x : E => x ^ (Fintype.card F + (Fintype.card E-1)/2)) (S : Set E)) :
    Fintype.card F ≤ S.card := by
  classical
  by_contra! short
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have order2 (x : E) : σ (σ x) = x := by
    rw [hσ,hσ, ← pow_mul, ← pow_two, ← size, FiniteField.pow_card]
  have notfixed : ∃ y : E, σ y ≠ y := by
    by_contra! he
    have surj : Function.Surjective (algebraMap F E) := fun x =>
      (pow_card_eq_iff_scalar F E x).1 ((hσ x).symm.trans (he x))
    have h := Fintype.card_le_of_surjective _ surj
    rw [size] at h
    have hs : 1 < Fintype.card F := Fintype.one_lt_card
    nlinarith
  obtain ⟨y,hy⟩ := notfixed
  let t := σ y-y
  have ht : t ≠ 0 := sub_ne_zero.mpr hy
  have hσt : σ t = -t := by simp [t,order2]
  have oddE : Odd (Fintype.card E) := size ▸ oddF.pow
  have two : (2:E) ≠ 0 := Ring.two_ne_zero (odd_char oddE)
  let ι := algebraMap F E
  obtain ⟨c,hc⟩ := missing S short (fun w => -(w + σ w)) (fun c : F => 2 * ι c)
    (fun _ _ h => ι.injective (mul_left_cancel₀ two h))
  obtain ⟨v,hv⟩ := missing S short (fun w => -(w - σ w)) (fun v : F => (2*t) * ι v)
    (fun _ _ h => ι.injective (mul_left_cancel₀ (mul_ne_zero two ht) h))
  let b := ι c + t * ι v
  have hb : σ b = ι c - t * ι v := by
    change σ ((algebraMap F E c) + t * algebraMap F E v) = _
    rw [map_add, map_mul, σ.commutes, σ.commutes, hσt]; ring
  obtain ⟨x,hx⟩ := blocks 1 b
  let z := x ^ exponent F E
  change z - 1*x - b ∈ S at hx
  rw [one_mul] at hx
  have signs : z = σ x ∨ z = -σ x := by
    by_cases h0 : x = 0
    · left; simp [z,h0, show exponent F E ≠ 0 from (Nat.add_pos_left Fintype.card_pos _).ne']
    rcases quadraticChar_dichotomy h0 with hp | hm
    · left; simp [z, branch_formula oddE σ hσ, hp]
    · right; simp [z, branch_formula oddE σ hσ, hm]
  rcases signs with h | h
  · apply hc _ hx
    rw [h, map_sub, map_sub, order2, hb]
    dsimp [b]; ring
  · apply hv _ hx
    rw [h, map_sub, map_sub, map_neg, order2, hb]
    dsimp [b]; ring

/-- The twisted relative Frobenius in dimension two is a permutation in every odd
characteristic: applying the very same power twice fixes every field element. -/
theorem power_involutive (oddF : Odd (Fintype.card F)) (size : Fintype.card E = Fintype.card F ^ 2) :
    Function.Involutive (fun x : E => x ^ (Fintype.card F + (Fintype.card E-1)/2)) := by
  let s := Fintype.card F
  obtain ⟨u,hu⟩ := oddF
  let k := u*(u+1)
  have order : Fintype.card E = 4*k+1 := by rw [size,hu]; dsimp [k]; ring
  have square : (s + (Fintype.card E-1)/2) * (s + (Fintype.card E-1)/2) =
      1 + (Fintype.card E-1)*(1+s+k) := by
    rw [order, Nat.add_sub_cancel, show 4*k/2 = 2*k by omega]
    have eq : s^2 = 4*k+1 := size.symm.trans order
    nlinarith only [eq]
  intro x
  change (x ^ (s + (Fintype.card E-1)/2)) ^ (s + (Fintype.card E-1)/2) = x
  by_cases hx : x = 0
  · have hp : 0 < s + (Fintype.card E-1)/2 := Nat.add_pos_left Fintype.card_pos _
    simp [hx,zero_pow hp.ne']
  rw [← pow_mul, square, pow_add, pow_mul, FiniteField.pow_card_sub_one_eq_one _ hx,
    one_pow, mul_one, pow_one]

/-- In every odd quadratic extension the projective blocking number of the mixed
monomial of exponent s+(s²−1)/2 is exactly s. -/
theorem minimum (oddF : Odd (Fintype.card F)) (size : Fintype.card E = Fintype.card F ^ 2) :
    AsgarliGhiocaYip.isPencilMinimum E (Fintype.card F + (Fintype.card E-1)/2) (Fintype.card F) := by
  classical
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have hd : 2 ≤ Fintype.card F + (Fintype.card E-1)/2 := by omega
  apply (AGY_minimum_iff hd _).2
  constructor
  · obtain ⟨π,split⟩ := exists_projection F E
    have nonzero : π ≠ 0 := by intro hz; simpa [hz] using split 1
    refine ⟨lift π {0}, ?_, (projectiveBlocks_iff_graphHits hd _).2 ?_⟩
    · rw [card_lift π split, cap_count π (by decide : 0 < 2) split size]
      simp
    · have h := projection_blocks oddF size π nonzero
      intro a b
      obtain ⟨x,hx⟩ := h a b
      exact ⟨x,(mem_lift π).2 (Finset.mem_singleton.2 hx)⟩
  · rintro _ ⟨S,rfl,hS⟩
    exact cardinal_lower oddF size S ((projectiveBlocks_iff_graphHits hd _).1 hS)

/-- A single ambient field with its two indicated subfields. For every odd
prime-power parameter t, both maps permute. The quadratic minimum is t³;
the cubic presentation already has a logarithmic upper bound. -/
theorem same_field_comparison {K : Type*} [Field K] [Fintype K] [Algebra K E]
    {t : ℕ} (ht : Odd t) (quadraticBase : Fintype.card F = t^3)
    (cubicBase : Fintype.card K = t^2) (ambient : Fintype.card E = t^6) :
    let r := (Fintype.card E-1)/2
    Function.Bijective (fun x:E => x^(t^3+r)) ∧ Function.Bijective (fun x:E => x^(t^2+r)) ∧
    AsgarliGhiocaYip.isPencilMinimum E (t^3+r) (t^3) ∧
    ∃ S : Finset E, ProjectiveBlocks (t^2+r) (S : Set E) ∧
      (S.card:ℝ) ≤ 4*Real.log (2*Fintype.card E)+1 := by
  have he : Fintype.card E = Fintype.card F^2 := by rw [quadraticBase,ambient,← pow_mul]
  have he' : Fintype.card E = Fintype.card K^3 := by rw [cubicBase,ambient,← pow_mul]
  have oddF : Odd (Fintype.card F) := quadraticBase ▸ ht.pow
  have four : 2^2 ∣ Fintype.card K-1 := by
    obtain ⟨k,hk⟩ := ht
    rw [cubicBase,hk]
    refine ⟨k^2+k,?_⟩
    rw [show (2*k+1)^2 = 4*(k^2+k)+1 by ring]
    omega
  have two : 2 ∣ Fintype.card K-1 := dvd_trans (by decide : 2 ∣ 2^2) four
  have perm₂ := (power_involutive (E := E) oddF he).bijective
  have perm₃ := ExtensionPhase.twist_permutation_of_square_dvd (by decide : 0 < 2) four he'
  have exact₂ := minimum (E := E) oddF he
  have upper₃ := ExtensionPhase.nondividing_projective_upper (by decide : 2 ≤ 2) two
    (by decide : ¬2 ∣ 3) he'
  rw [quadraticBase] at perm₂ exact₂
  rw [cubicBase] at perm₃ upper₃
  exact ⟨perm₂,perm₃,exact₂,by convert upper₃ using 6; norm_num⟩

end BlockingCurves.PhaseQuadratic
