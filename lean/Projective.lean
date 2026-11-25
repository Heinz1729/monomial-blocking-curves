import GeneralGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace BlockingCurves
variable {E : Type*} [Field E]

/-- All homogeneous line equations over E, and nonzero homogeneous point representatives.
    The two equations are homogeneous, so the predicate descends to projective points. -/
def ProjectiveBlocks (d : ℕ) (S : Set E) : Prop :=
  ∀ a b c : E, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ∃ α ∈ S, ∃ X Y Z : E, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧
      a*X + b*Y + c*Z = 0 ∧ Y * Z^(d-1) = X^d - α * Z^d

/-- The homogeneous projective problem is equivalent to the finite-slope test. -/
theorem projectiveBlocks_iff_graphHits {d : ℕ} (hd : 2 ≤ d) (S : Set E) :
    ProjectiveBlocks d S ↔ GraphHits (fun x : E => x^d) S := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k+2 := ⟨d-2, by omega⟩
  constructor
  · intro hh m t
    obtain ⟨α, hα, X, Y, Z, hn, hl, hc⟩ := hh (-m) 1 (-t) (Or.inr (Or.inl one_ne_zero))
    have hz : Z ≠ 0 := by
      intro he
      subst Z
      simp at hc
      have hx : X = 0 := by simpa using hc.symm
      subst X
      have hy : Y = 0 := by simpa using hl
      simp [hy] at hn
    have hz' : Z^(k+2) ≠ 0 := pow_ne_zero _ hz
    have hcurve : Y/Z = (X/Z)^(k+2) - α := by
      rw [div_pow, div_eq_iff hz]
      field_simp [hz, hz']
      change Y * Z^(k+1) = X^(k+2) - α * Z^(k+2) at hc
      simp only [pow_succ] at hc ⊢
      linear_combination Z * hc
    have hline : Y/Z = m*(X/Z) + t := by
      field_simp [hz]
      linear_combination hl
    refine ⟨X/Z, ?_⟩
    have he : (X/Z)^(k+2) - m*(X/Z) - t = α := by
      linear_combination hline - hcurve
    rwa [he]
  · intro hh a b c _
    by_cases hb : b = 0
    · obtain ⟨x, hx⟩ := hh 0 0
      refine ⟨_, hx, 0, 1, 0, Or.inr (Or.inl one_ne_zero), ?_, ?_⟩ <;> simp [hb]
    · let m := -a / b
      let t := -c / b
      obtain ⟨x, hx⟩ := hh m t
      refine ⟨_, hx, x, m*x+t, 1, Or.inr (Or.inr one_ne_zero), ?_, ?_⟩
      · dsimp [m,t]
        field_simp [hb]
        ring
      · simp
        ring

end BlockingCurves




