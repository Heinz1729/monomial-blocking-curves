import Paper

namespace BlockingCurves
variable {E : Type*} [Field E]

/-- Every rational line has a rational point outside the union of the selected curves. -/
def NoFullProjectiveLine (d : ℕ) (S : Set E) : Prop :=
  ∀ a b c : E, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ∃ X Y Z : E, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧ a*X + b*Y + c*Z = 0 ∧
      ∀ α ∈ S, Y * Z^(d-1) ≠ X^d - α * Z^d

theorem noFullProjectiveLine_iff {d : ℕ} (hd : 2 ≤ d) (S : Set E) :
    NoFullProjectiveLine d S ↔ S ≠ Set.univ := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k+2 := ⟨d-2, by omega⟩
  constructor
  · rintro h rfl
    obtain ⟨X, Y, Z, _, hX, hn⟩ := h 1 0 0 (Or.inl one_ne_zero)
    have hx : X = 0 := by simpa using hX
    subst X
    by_cases hz : Z = 0
    · subst Z
      exact hn 0 (Set.mem_univ _) (by simp)
    · apply hn (-(Y*Z^(k+1)) / Z^(k+2)) (Set.mem_univ _)
      simp [hz]
  · intro hs a b c hline
    obtain ⟨s, hs⟩ := (Set.ne_univ_iff_exists_not_mem S).mp hs
    by_cases hb : b = 0
    · subst b
      by_cases ha : a = 0
      · subst a
        exact ⟨1, 0, 0, Or.inl one_ne_zero, by simp, fun α _ => by simp⟩
      · let x := -c/a
        refine ⟨x, x^(k+2)-s, 1, Or.inr (Or.inr one_ne_zero), ?_, ?_⟩
        · dsimp [x]
          field_simp [ha]
          ring
        · intro α hα he
          have he' : s = α := by simpa using he
          exact hs (he' ▸ hα)
    · exact ⟨b, -a, 0, Or.inl hb, by ring, fun α _ => by simp [(pow_ne_zero (k+2) hb).symm]⟩

theorem frobenius_divisible_only_univ (p h e : ℕ) [hp : Fact p.Prime]
    (hh : h ≠ 0) (he : e ≠ 0) (hdiv : h ∣ e)
    (S : Finset (GaloisField p h)) (hS : ProjectiveBlocks (p^e) (S : Set (GaloisField p h))) :
    S = Finset.univ := by
  have hm := (projective_prime_power_minimum p h e hh he).2
    (show S.card ∈ _ from ⟨S, rfl, hS⟩)
  have hg : h.gcd e = h := Nat.gcd_eq_left hdiv
  rw [hg, Nat.div_self (Nat.pos_of_ne_zero hh), Nat.mul_one] at hm
  have hpos := Nat.pow_pos hp.out.pos (n := h)
  have hcard := S.card_le_univ
  rw [GaloisField.card p h hh] at hcard
  apply Finset.eq_univ_of_card
  rw [GaloisField.card p h hh]
  omega

private theorem affine_count_lt_power {b n : ℕ} (hb : 2 ≤ b) (hn : 2 ≤ n) :
    (b-1)*n+1 < b^n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+2 := ⟨n-2, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, b = a+2 := ⟨b-2, by omega⟩
  clear hn hb
  induction k with
  | zero => simp [pow_two]; nlinarith
  | succ k ih =>
    have hp : 2 ≤ (a+2)^(k+2) := Nat.one_lt_pow (by omega) (by omega)
    rw [show k+1+2 = (k+2)+1 by omega, pow_succ]
    rw [show a+2-1=a+1 by omega] at ih ⊢
    nlinarith [Nat.mul_le_mul_left a hp]

theorem nontrivial_projective_prime_power_minimum (p h e : ℕ) [hp : Fact p.Prime]
    (hh : h ≠ 0) (he : e ≠ 0) (hdiv : ¬h ∣ e) :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField p h), S.card = r ∧
      ProjectiveBlocks (p^e) (S : Set (GaloisField p h)) ∧
      NoFullProjectiveLine (p^e) (S : Set (GaloisField p h))}
      ((p ^ (h.gcd e) - 1) * (h / h.gcd e) + 1) := by
  have hm := projective_prime_power_minimum p h e hh he
  constructor
  · obtain ⟨S, hc, hS⟩ := hm.1
    refine ⟨S, hc, hS, (noFullProjectiveLine_iff (Nat.one_lt_pow he hp.out.one_lt) _).mpr ?_⟩
    intro hall
    have hfin : S = Finset.univ := Finset.coe_injective (by simpa using hall)
    have hg : 0 < h.gcd e := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hh)
    have hfac := Nat.div_mul_cancel (Nat.gcd_dvd_left h e)
    have hn : 2 ≤ h / h.gcd e := by
      by_contra! hl
      interval_cases h / h.gcd e <;> simp_all
      exact hdiv (hfac ▸ Nat.gcd_dvd_right h e)
    have hlt := affine_count_lt_power (Nat.one_lt_pow (Nat.ne_of_gt hg) hp.out.one_lt) hn
    rw [← pow_mul, Nat.mul_comm (h.gcd e) (h / h.gcd e), hfac] at hlt
    rw [hfin, Finset.card_univ, GaloisField.card p h hh] at hc
    omega
  · rintro r ⟨S, hc, hS, _⟩
    exact hm.2 ⟨S, hc, hS⟩

end BlockingCurves
