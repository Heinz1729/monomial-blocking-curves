import NormPencil
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Collision and sampling bounds for a monomial pencil with varying degree. -/
namespace BlockingCurves.PencilCollisionCover

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

/-- The same horizontal predicate and minimum are used in the norm-family formula. -/
abbrev horizontalHits (d : ℕ) (S : Finset F) := NormPencil.PowerCover d S

abbrev horizontalMinimum := NormPencil.coverNumber

theorem horizontalMinimum_spec (F : Type*) [Field F] [Fintype F] (d : ℕ) :
    IsLeast {n : ℕ | ∃ S : Finset F, S.card = n ∧ horizontalHits d S}
      (horizontalMinimum F d) := by
  classical
  refine ⟨NormPencil.coverNumber_attained F d, ?_⟩
  rintro _ ⟨S,rfl,hS⟩
  exact NormPencil.coverNumber_le hS

local instance : DecidableEq F := Classical.decEq _

/-- A nonempty multiplicative power fibre, normalized at any one of its points,
injects into the roots of unity of order gcd(k,q-1). -/
theorem scaled_power_fibre_le (k : ℕ) (hk : 0 < k) (a m : F) (hm : m ≠ 0) :
    (Finset.univ.filter (fun z : F => a * z ^ k = m)).card ≤
      k.gcd (Fintype.card F - 1) := by
  classical
  let T := Finset.univ.filter (fun z : F => a * z ^ k = m)
  change T.card ≤ _
  by_cases hT : T.Nonempty
  · obtain ⟨w, hw⟩ := hT
    have eqn {z : F} (hz : z ∈ T) : a * z ^ k = m := (Finset.mem_filter.mp hz).2
    have nz {z : F} (hz : z ∈ T) : z ≠ 0 := by
      rintro rfl
      simpa [zero_pow hk.ne'] using (eqn hz).trans_ne hm
    have ha : a ≠ 0 := by
      rintro rfl
      simpa using (eqn hw).trans_ne hm
    let g := k.gcd (Fintype.card F - 1)
    have hg : 0 < g := Nat.gcd_pos_of_pos_left _ hk
    calc
      T.card ≤ (Polynomial.nthRootsFinset g F).card := by
        apply Finset.card_le_card_of_inj_on (fun z : F => z / w)
        · intro z hz
          apply (Polynomial.mem_nthRootsFinset hg).2
          apply orderOf_dvd_iff_pow_eq_one.mp
          apply Nat.dvd_gcd
          · apply orderOf_dvd_iff_pow_eq_one.mpr
            rw [div_pow, (mul_left_cancel₀ ha ((eqn hz).trans (eqn hw).symm)), div_self (pow_ne_zero _ (nz hw))]
          · exact orderOf_dvd_iff_pow_eq_one.mpr
              (FiniteField.pow_card_sub_one_eq_one _ (div_ne_zero (nz hz) (nz hw)))
        · intro z _ v _ he
          exact (div_left_inj' (nz hw)).mp he
      _ ≤ g := by
        rw [Polynomial.nthRootsFinset_def]
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]

private def value (d : ℕ) (m b x : F) := x ^ d - m*x - b

/-- Ordered distinct inputs on which a function has the same value. -/
def offDiagonal (f : F → F) : Finset (F × F) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

/-- For an ordered collision let z=x-y and t=y/z. For fixed t the equation
is ((t+1)^d-t^d) z^(d-1) = m, and z recovers the ordered pair. -/
theorem off_diagonal_collisions_le (d : ℕ) (hd : 2 ≤ d) (m b : F) (hm : m ≠ 0) :
    (offDiagonal (fun x : F => x^d-m*x-b)).card ≤ (d-1).gcd (Fintype.card F-1) * Fintype.card F := by
  classical
  let slope (p : F × F) := p.2 / (p.1-p.2)
  let fibre (t : F) := (offDiagonal (value d m b)).filter (fun p => slope p = t)
  have coords {t : F} {p : F × F} (hp : p ∈ fibre t) :
      p.1-p.2 ≠ 0 ∧ t*(p.1-p.2) = p.2 ∧ (t+1)*(p.1-p.2) = p.1 := by
    obtain ⟨hc, ht⟩ := Finset.mem_filter.mp hp
    have hn := sub_ne_zero.mpr (Finset.mem_filter.mp hc).2.1
    have hy : t*(p.1-p.2) = p.2 := (eq_div_iff hn).mp ht.symm
    exact ⟨hn, hy, by linear_combination hy⟩
  apply (Finset.card_le_mul_card_image_of_maps_to (t := Finset.univ)
    (f := slope) (fun _ _ => Finset.mem_univ _) _ ?_).trans_eq (by rw [Finset.card_univ])
  intro t _
  apply le_trans _ (scaled_power_fibre_le (d-1) (by omega) ((t+1)^d-t^d) m hm)
  apply Finset.card_le_card_of_inj_on (fun p : F × F => p.1-p.2)
  · intro p hp
    obtain ⟨hn, hy, hx⟩ := coords hp
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2
    change p.1^d-m*p.1-b = p.2^d-m*p.2-b at hc
    have hpow : ((t+1)^d-t^d)*(p.1-p.2)^d = m*(p.1-p.2) := by
      rw [sub_mul, ← mul_pow, ← mul_pow, hx, hy]
      linear_combination hc
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, mul_right_cancel₀ hn ?_⟩
    rw [mul_assoc, ← pow_succ, show d-1+1 = d by omega]
    exact hpow
  · intro p hp r hr he
    obtain ⟨_, hy, hx⟩ := coords hp
    obtain ⟨_, hy', hx'⟩ := coords hr
    exact Prod.ext (by rw [← hx, ← hx', he]) (by rw [← hy, ← hy', he])

/-- Cauchy–Schwarz on fibre sizes. The diagonal contributes exactly q
ordered pairs for every function. -/
theorem image_collision_bound (f : F → F) :
    (Fintype.card F)^2 ≤ (Finset.univ.image f).card * (Fintype.card F + (offDiagonal f).card) := by
  classical
  let I := Finset.univ.image f
  let R (y : F) := Finset.univ.filter (fun x : F => f x = y)
  let C := (Finset.univ : Finset (F × F)).filter (fun p => f p.1 = f p.2)
  have hfirst : Fintype.card F = ∑ y ∈ I, (R y).card := by
    simpa [R] using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := I) (f := f) (fun x _ => Finset.mem_image_of_mem _ (Finset.mem_univ x)))
  have hsecond : C.card = ∑ y ∈ I, (R y).card^2 := by
    rw [Finset.card_eq_sum_card_fiberwise (s := C) (t := I) (f := fun p => f p.1)
      (fun p _ => Finset.mem_image_of_mem _ (Finset.mem_univ p.1))]
    apply Finset.sum_congr rfl
    intro y _
    rw [sq, ← Finset.card_product]
    congr 1
    ext p
    simp only [C, R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨fun ⟨he,hy⟩ => ⟨hy, he.symm.trans hy⟩, fun ⟨hx,hy⟩ => ⟨hx.trans hy.symm, hx⟩⟩
  have cover : C ⊆ (Finset.univ : Finset F).diag ∪ offDiagonal f := by
    intro p hp
    by_cases he : p.1 = p.2
    · exact Finset.mem_union_left _ (Finset.mem_diag.mpr ⟨Finset.mem_univ _, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, he, (Finset.mem_filter.mp hp).2⟩)
  have hC : C.card ≤ Fintype.card F + (offDiagonal f).card := by
    simpa using (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ : F => (1:ℕ)) (fun y => (R y).card)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, ← hfirst, ← hsecond] at hc
  exact hc.trans (Nat.mul_le_mul_left I.card hC)

/-- A nonhorizontal line's value set has at least q/(h+1) elements, even when
the characteristic is bad or the degree varies with the field. -/
theorem nonzero_slope_image_bound (d : ℕ) (hd : 2 ≤ d) (m b : F) (hm : m ≠ 0) :
    Fintype.card F ≤ ((Finset.univ : Finset F).image (fun x => x^d-m*x-b)).card *
      ((d-1).gcd (Fintype.card F-1) + 1) := by
  classical
  let f := value d m b
  have hc := image_collision_bound f
  have hp := off_diagonal_collisions_le d hd m b hm
  have hC : Fintype.card F + (offDiagonal f).card ≤
      Fintype.card F * ((d-1).gcd (Fintype.card F-1)+1) := by
    simpa [Nat.mul_add, Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left hp (Fintype.card F)
  have hn := hc.trans (Nat.mul_le_mul_left _ hC)
  rw [sq, ← Nat.mul_assoc, Nat.mul_comm (Finset.univ.image f).card, Nat.mul_assoc] at hn
  exact Nat.le_of_mul_le_mul_left hn Fintype.card_pos

/-- Number of admissible additional ordered samples for the varying-degree bound. -/
def supplementSize (q h : ℕ) : ℕ :=
  ⌈2 * Real.log q / Real.log (1 + 1/(h:ℝ))⌉₊

private theorem sampling_strict (q h H : ℕ) (hq : 1 < q) (hh : 0 < h)
    (hH : H * (h+1) ≤ q*h) :
    q*(q-1)*H^(supplementSize q h) < q^(supplementSize q h) := by
  let k := supplementSize q h
  let a : ℝ := 1+1/(h:ℝ)
  have hq0 : 0 < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hh0 : 0 < (h:ℝ) := by exact_mod_cast hh
  have ha : 1 < a := by dsimp [a]; linarith only [one_div_pos.mpr hh0]
  have ha0 : 0 < a := by linarith
  have hk : 2*Real.log q ≤ (k:ℝ)*Real.log a := by
    apply (div_le_iff (Real.log_pos ha)).mp
    exact Nat.le_ceil _
  have hqpow : (q:ℝ)^2 ≤ a^k := by
    apply (Real.log_le_log_iff (pow_pos hq0 _) (pow_pos ha0 _)).mp
    rw [Real.log_pow, Real.log_pow]
    exact_mod_cast hk
  have haH : a * (H:ℝ) ≤ q := by
    have hcast : (H:ℝ) * (h+1) ≤ q*h := by exact_mod_cast hH
    dsimp [a]
    field_simp
    apply (div_le_iff hh0).2
    linarith only [hcast]
  have hmain : q^2*H^k ≤ q^k := by
    have ht := mul_le_mul_of_nonneg_right hqpow (pow_nonneg (Nat.cast_nonneg H : (0:ℝ) ≤ H) k)
    rw [← mul_pow] at ht
    exact_mod_cast ht.trans (pow_le_pow_left (by positivity) haH k)
  change q*(q-1)*H^k < q^k
  by_cases hz : H^k = 0
  · simp [hz, Nat.pow_pos (by omega : 0 < q)]
  · have hs : q*(q-1) < q^2 := by
      rw [sq]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    exact (Nat.mul_lt_mul_of_pos_right hs (Nat.pos_of_ne_zero hz)).trans_le hmain

/-- Any horizontal cover extends to a full projective cover with the stated
supplement. Sampling with replacement costs at most one new parameter per draw. -/
theorem extend_horizontal_cover (d : ℕ) (hd : 2 ≤ d) (T : Finset F) (hT : horizontalHits d T) :
    ∃ S : Finset F, T ⊆ S ∧ ProjectiveBlocks d (S : Set F) ∧
      S.card ≤ T.card + supplementSize (Fintype.card F) ((d-1).gcd (Fintype.card F-1)) := by
  classical
  let q := Fintype.card F
  let h := (d-1).gcd (q-1)
  let k := supplementSize q h
  let H := q*h/(h+1)
  let L := Fˣ × F
  let miss (m b : F) := Finset.univ \ (Finset.univ.image (value d m b))
  have hline (m b : F) (hm : m ≠ 0) : (miss m b).card ≤ H := by
    apply (Nat.le_div_iff_mul_le (Nat.succ_pos _)).2
    have hc : (miss m b).card + (Finset.univ.image (value d m b)).card = q :=
      (Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _)).trans Finset.card_univ
    have hi := nonzero_slope_image_bound d hd m b hm
    change q ≤ (Finset.univ.image (value d m b)).card*(h+1) at hi
    change (miss m b).card*(h+1) ≤ q*h
    have hs : (miss m b).card*(h+1) + (Finset.univ.image (value d m b)).card*(h+1) =
        q*h+q := by rw [← Nat.add_mul, hc, Nat.mul_add, Nat.mul_one]
    omega
  let bad (l : L) : Finset (Fin k → F) := Fintype.piFinset (fun _ => miss (l.1:F) l.2)
  let U := (Finset.univ : Finset L).biUnion bad
  have hbad (l : L) : (bad l).card ≤ H^k := by
    dsimp [bad]
    simpa using pow_le_pow_left' (hline _ _ l.1.ne_zero) k
  have hcard : U.card < Fintype.card (Fin k → F) := by
    have hb := Finset.card_biUnion_le_card_mul (Finset.univ : Finset L) bad (H^k) (fun l _ => hbad l)
    have hc : Fintype.card L = q*(q-1) := by simp [L,q,Fintype.card_units,Nat.mul_comm]
    have hq : 1 < q := Fintype.one_lt_card
    have hh : 0 < h := Nat.gcd_pos_of_pos_left _ (by omega)
    rw [Finset.card_univ, hc] at hb
    simpa [U, q, k] using hb.trans_lt (sampling_strict q h H hq hh (Nat.div_mul_le_self _ _))
  obtain ⟨f,hf⟩ : ∃ f : Fin k → F, f ∉ U := by
    by_contra! hall
    rw [Finset.eq_univ_of_forall hall, Finset.card_univ] at hcard
    exact (Nat.lt_irrefl _) hcard
  have hsample : (Finset.univ.image f).card ≤ k := by
    simpa using Finset.card_image_le (s := Finset.univ) (f := f)
  refine ⟨T ∪ Finset.univ.image f, Finset.subset_union_left _ _, (projectiveBlocks_iff_graphHits hd _).2 ?_,
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left hsample _)⟩
  intro m b
  by_cases hm : m = 0
  · obtain ⟨x,hx⟩ := hT b
    exact ⟨x, Finset.mem_union_left _ (by simpa [hm] using hx)⟩
  · let l : L := (Units.mk0 m hm,b)
    have hn : f ∉ bad l := fun he => hf (Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,he⟩)
    rw [show bad l = Fintype.piFinset (fun _ : Fin k => miss m b) from rfl, Fintype.mem_piFinset] at hn
    push_neg at hn
    obtain ⟨i,hi⟩ := hn
    simp [miss] at hi
    obtain ⟨x,hx⟩ := hi
    exact ⟨x,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx.symm⟩)⟩

/-- The minimum in the independent projective specification lies between the
horizontal minimum and that minimum plus the rounded logarithmic supplement. -/
theorem variable_degree_minimum_gap (F : Type*) [Field F] [Fintype F] (d : ℕ) (hd : 2 ≤ d) :
    ∃ B : ℕ, AsgarliGhiocaYip.isPencilMinimum F d B ∧ horizontalMinimum F d ≤ B ∧
      B - horizontalMinimum F d ≤ supplementSize (Fintype.card F) ((d-1).gcd (Fintype.card F-1)) := by
  classical
  obtain ⟨T, hcard, hT⟩ := (horizontalMinimum_spec F d).1
  obtain ⟨S, _, hS, hsize⟩ := extend_horizontal_cover d hd T hT
  let P (n : ℕ) := ∃ U : Finset F, U.card = n ∧ ProjectiveBlocks d (U : Set F)
  have hS' : P S.card := ⟨S,rfl,hS⟩
  have hex : ∃ n, P n := ⟨_,hS'⟩
  let B := Nat.find hex
  obtain ⟨U, hU, hcover⟩ := Nat.find_spec hex
  refine ⟨B, (AGY_minimum_iff hd _).2 ⟨Nat.find_spec hex, fun _ h => Nat.find_min' hex h⟩,
    (horizontalMinimum_spec F d).2 ⟨U,hU,?_⟩, ?_⟩
  · intro b
    simpa using (projectiveBlocks_iff_graphHits hd _).1 hcover 0 b
  · have := Nat.find_min' hex hS'
    change Nat.find hex - _ ≤ _
    omega

end
end BlockingCurves.PencilCollisionCover
