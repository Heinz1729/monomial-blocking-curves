import NormPencil
import Frobenius
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The norm exponent, its ground-field values, and projective minima. -/
namespace BlockingCurves.NormPencil

open scoped BigOperators
open Polynomial
attribute [local instance] Classical.propDecidable

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The geometric sum 1+s+...+s^(n-1), represented without natural division. -/
def normExponent (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => normExponent s n + s ^ n

theorem normExponent_mul (s n : ℕ) (hs : 1 ≤ s) :
    normExponent s n * (s - 1) + 1 = s ^ n := by
  induction n with
  | zero => simp [normExponent]
  | succ n ih =>
    simp only [normExponent, add_mul, pow_succ]
    have he := Nat.sub_add_cancel hs
    nlinarith [congrArg (fun t => s ^ n * t) he]

theorem normExponent_eq_div (s n : ℕ) (hs : 1 < s) :
    normExponent s n = (s ^ n - 1) / (s - 1) := by
  have he := normExponent_mul s n hs.le
  rw [← he, Nat.add_sub_cancel, Nat.mul_div_cancel _ (by omega)]

theorem normExponent_pos {s n : ℕ} (hs : 0 < s) (hn : 0 < n) :
    0 < normExponent s n := by
  cases n with
  | zero => omega
  | succ n => exact Nat.add_pos_right _ (pow_pos hs n)

theorem normExponent_two_le {s n : ℕ} (hs : 1 < s) (hn : 2 ≤ n) :
    2 ≤ normExponent s n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp [normExponent]; omega
  | succ k ih => exact (ih (by omega)).trans (Nat.le_add_right _ _)

theorem scalar_norm_power (u : F) (n : ℕ) :
    u ^ normExponent (Fintype.card F) n = u ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [normExponent, pow_add, ih, FiniteField.pow_card_pow, pow_succ]

/-- In any extension of the stated cardinality, every norm power belongs to the subfield. -/
theorem norm_in_ground {n : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F ^ n) (x : E) :
    ∃ u : F, algebraMap F E u = x ^ normExponent (Fintype.card F) n := by
  let s := Fintype.card F
  let D := normExponent s n
  have hs : 1 < s := Fintype.one_lt_card
  have he : D * (s-1) = Fintype.card E - 1 := by
    have haux : D * (s - 1) + 1 = s ^ n := normExponent_mul s n hs.le
    change Fintype.card E = s ^ n at size
    rw [size, ← haux, Nat.add_sub_cancel]
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx, zero_pow (normExponent_pos (s := s) (by omega) hn).ne']⟩
  apply (pow_card_eq_iff_scalar F E _).1
  change (x ^ D) ^ s = x ^ D
  calc
    _ = (x ^ D) ^ (s-1) * x ^ D := by rw [← pow_succ, Nat.sub_add_cancel hs.le]
    _ = x ^ D := by rw [← pow_mul, he, FiniteField.pow_card_sub_one_eq_one _ hx, one_mul]

/-- Every ground-field element occurs as an actual norm power. -/
theorem norm_power_surjective {n : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F ^ n) (u : F) :
    ∃ x : E, x ^ normExponent (Fintype.card F) n = algebraMap F E u := by
  let s := Fintype.card F
  let D := normExponent s n
  have hs : 1 < s := Fintype.one_lt_card
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu, zero_pow (normExponent_pos (s := s) (by omega) hn).ne']⟩
  let e : Eˣ := Units.mk0 (algebraMap F E u) (by simpa using (algebraMap F E).injective.ne hu)
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  obtain ⟨k,hk⟩ : e ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 (hg e)
  change g ^ k = e at hk
  have he : e ^ (s-1) = 1 := by
    apply Units.ext
    change (algebraMap F E u) ^ (Fintype.card F - 1) = _
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one u hu, map_one]
    rfl
  have horder : orderOf g = D * (s-1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Fintype.card_units, size]
    have haux : D * (s-1) + 1 = s ^ n := normExponent_mul s n hs.le
    change s ^ n - 1 = _
    rw [← haux, Nat.add_sub_cancel]
  have hdvd : D ∣ k := by
    apply Nat.dvd_of_mul_dvd_mul_right (show 0 < s-1 by omega)
    rw [← horder]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, hk, he]
  obtain ⟨j,hj⟩ := hdvd
  refine ⟨(g : E) ^ j, ?_⟩
  change (g.val ^ j) ^ D = e.val
  rw [← pow_mul, Nat.mul_comm, ← hj, ← Units.val_pow_eq_pow_val, hk]

theorem cap_count (π : E →ₗ[F] F) {n : ℕ} (hn : 0 < n)
    (split : ∀ c : F, π (algebraMap F E c) = c)
    (size : Fintype.card E = Fintype.card F ^ n) :
    Fintype.card (LinearMap.ker π) = Fintype.card F ^ (n-1) := by
  have h := card_lift π split (Finset.univ : Finset F)
  have hu : lift π (Finset.univ : Finset F) = Finset.univ := by
    ext x
    simp [mem_lift]
  rw [hu, Finset.card_univ, Finset.card_univ, size] at h
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_sub_one, pow_succ] at h ⊢
  exact Nat.eq_of_mul_eq_mul_right Fintype.card_pos h.symm

/-- Universal norm-family lower bound; this only uses the horizontal lines. -/
theorem norm_horizontal_lower {n m : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F ^ n)
    (S : Finset E) (hS : ∀ b : E, ∃ x : E, x ^ (m * normExponent (Fintype.card F) n) - b ∈ S) :
    Fintype.card F ^ (n-1) * coverNumber F m ≤ S.card := by
  obtain ⟨π,split⟩ := exists_projection F E
  rw [← cap_count π hn split size]
  apply horizontal_lower π split _ S hS
  intro x
  obtain ⟨u,hu⟩ := norm_in_ground hn size x
  exact ⟨u, by rw [map_pow, hu, Nat.mul_comm, pow_mul]⟩

/-- Exact horizontal optimum in every extension, even when the norm has no
coprimality property on the embedded ground field. -/
theorem norm_horizontal_minimum {n m : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F ^ n) :
    IsLeast {k : ℕ | ∃ S : Finset E, S.card = k ∧
      ∀ b : E, ∃ x : E, x ^ (m * normExponent (Fintype.card F) n) - b ∈ S}
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  obtain ⟨π,split⟩ := exists_projection F E
  obtain ⟨T,hcard,hT⟩ := coverNumber_attained F m
  constructor
  · refine ⟨lift π T, ?_, ?_⟩
    · rw [card_lift π split, cap_count π hn split size, hcard]
    · intro b
      obtain ⟨u,hu⟩ := hT (π b)
      obtain ⟨x,hx⟩ := norm_power_surjective hn size u
      refine ⟨x,(mem_lift π).2 ?_⟩
      rwa [map_sub, Nat.mul_comm, pow_mul, hx, ← map_pow, split]
  · rintro _ ⟨S,rfl,hS⟩
    exact norm_horizontal_lower hn size S hS

private theorem pow_surject {n : ℕ} (hn : 0 < n) (h : (Fintype.card F - 1).Coprime n)
    (u : F) : ∃ c : F, c ^ n = u := by
  by_cases hu : u = 0
  · exact ⟨0, by simp [hu, zero_pow hn.ne']⟩
  have huCard : (Nat.card Fˣ).Coprime n := by simpa [Nat.card_eq_fintype_card, Fintype.card_units] using h
  obtain ⟨v, hv⟩ := huCard.pow_left_bijective.surjective (Units.mk0 u hu)
  exact ⟨v, congrArg Units.val hv⟩

/-- A nonzero vector in the kernel of x ↦ π(ax). Only the strict extension size matters. -/
private theorem kernel_vector (π : E →ₗ[F] F) (larger : Fintype.card F < Fintype.card E)
    (a : E) : ∃ y : E, y ≠ 0 ∧ π (a*y) = 0 := by
  by_contra! h
  have inj : Function.Injective (fun x : E => π (a*x)) := by
    intro x y he
    by_contra hxy
    apply h (x-y) (sub_ne_zero.mpr hxy)
    rw [mul_sub, map_sub, sub_eq_zero]
    exact he
  exact (Nat.not_le_of_gt larger) (Fintype.card_le_of_injective _ inj)

theorem coprime_kernel {n m : ℕ} (hn : 2 ≤ n)
    (size : Fintype.card E = Fintype.card F ^ n) (cop : (Fintype.card F - 1).Coprime n)
    (π : E →ₗ[F] F) (a : E) (u : F) :
    ∃ x : E, π (a*x) = 0 ∧
      x ^ (m * normExponent (Fintype.card F) n) = algebraMap F E (u ^ m) := by
  have hs : 1 < Fintype.card F := Fintype.one_lt_card
  have larger : Fintype.card F < Fintype.card E := by
    rw [size]
    simpa using (Nat.pow_lt_pow_right hs (show 1 < n by omega))
  obtain ⟨y,hy,hy0⟩ := kernel_vector π larger a
  obtain ⟨v,hv⟩ := norm_in_ground (by omega : 0 < n) size y
  have hv0 : v ≠ 0 := fun hz => (pow_ne_zero _ hy) (hv.symm.trans (by simp [hz]))
  obtain ⟨c,hc⟩ := pow_surject (by omega : 0 < n) cop (u / v)
  refine ⟨c • y, ?_, ?_⟩
  · rw [mul_smul_comm, map_smul, hy0, smul_zero]
  · rw [Algebra.smul_def, Nat.mul_comm, pow_mul, mul_pow, ← map_pow,
      scalar_norm_power, hc, ← hv, ← map_mul, div_mul_cancel₀ _ hv0, map_pow]

/-- An optimizer of norm-family size contains no full rational projective line. -/
theorem norm_optimum_no_line {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) (S : Finset E)
    (hcard : S.card = Fintype.card F ^ (n-1) * coverNumber F m) :
    NoFullProjectiveLine (m * normExponent (Fintype.card F) n) (S : Set E) := by
  apply (noFullProjectiveLine_iff ((normExponent_two_le Fintype.one_lt_card hn).trans
    (Nat.le_mul_of_pos_left _ hm)) _).2
  intro hall
  have hu : S = Finset.univ := by ext x; simpa using (Set.ext_iff.1 hall x)
  have hs : 0 < Fintype.card F := Fintype.card_pos
  have hlt := Nat.mul_lt_mul_of_pos_left (coverNumber_lt_card (F := F) hm)
    (pow_pos hs (n-1))
  have he : Fintype.card F ^ (n-1) * Fintype.card F = Fintype.card E := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n), ← size]
  rw [← hcard, he, hu, Finset.card_univ] at hlt
  exact hlt.false

/-- Horizontal optimality is sufficient as soon as optimal lifts attain all slopes. -/
theorem minimum_of_kernel {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n)
    (hker : ∀ (π : E →ₗ[F] F) (a : E) (u : F), ∃ x : E, π (a*x) = 0 ∧
      x ^ (m * normExponent (Fintype.card F) n) = algebraMap F E (u ^ m)) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) n)
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  have hd : 2 ≤ m * normExponent (Fintype.card F) n :=
    (normExponent_two_le Fintype.one_lt_card hn).trans (Nat.le_mul_of_pos_left _ hm)
  apply (AGY_minimum_iff hd _).2
  obtain ⟨π,split⟩ := exists_projection F E
  obtain ⟨T,hcard,hT⟩ := coverNumber_attained F m
  constructor
  · refine ⟨lift π T, ?_, (projectiveBlocks_iff_graphHits hd _).2 ?_⟩
    · rw [card_lift π split, hcard, cap_count π (by omega) split size]
    · exact graphHits_lift π split T hT (hker π)
  · rintro _ ⟨S,rfl,hS⟩
    apply norm_horizontal_lower (by omega : 0 < n) size S
    intro b
    simpa using (projectiveBlocks_iff_graphHits hd _).1 hS 0 b

/-- A single explicitly constructed projection lift is optimal when the base-scalar
action is transitive on nonzero norm values. -/
theorem coprime_norm_minimum {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) (cop : (Fintype.card F - 1).Coprime n) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) n)
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  exact minimum_of_kernel hn hm size (coprime_kernel hn size cop)

end BlockingCurves.NormPencil
