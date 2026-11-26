import ProblemStatement
import NontrivialPencil
import GeometricIrreducibility

namespace BlockingCurves

variable {F : Type*} [Field F]

theorem graphHits_iff_AGY (d : ℕ) (S : Set F) :
    GraphHits (fun x : F => x ^ d) S ↔ AsgarliGhiocaYip.hitsValueSets d S := by
  constructor
  · intro h u v
    obtain ⟨x, hx⟩ := h (-u) (-v)
    refine ⟨_, ?_, x, rfl⟩
    simpa only [neg_mul, sub_neg_eq_add] using hx
  · intro h m b
    obtain ⟨_, hS, x, rfl⟩ := h (-m) (-b)
    refine ⟨x, ?_⟩
    simpa only [neg_mul, ← sub_eq_add_neg] using hS

/-- The manuscript's homogeneous blocking predicate answers the source specification. -/
theorem projectiveBlocks_iff_AGY {d : ℕ} (hd : 2 ≤ d) (S : Set F) :
    ProjectiveBlocks d S ↔ AsgarliGhiocaYip.hitsValueSets d S :=
  (projectiveBlocks_iff_graphHits hd S).trans (graphHits_iff_AGY d S)

open AsgarliGhiocaYip

theorem AGY_form_eq (d : ℕ) (α : F) : pencilForm d α = monomialCurveForm d α := by
  unfold pencilForm monomialCurveForm
  ring

theorem AGY_admissible {d : ℕ} (hd : 2 ≤ d) (α : F) : admissible d (pencilForm d α) := by
  rw [AGY_form_eq]
  have hp : 0 < d := by omega
  have hh := monomialCurveForm_isHomogeneous d hp α
  exact ⟨hd, hh, hh.totalDegree (monomialCurveForm_irreducible d hp α).ne_zero,
    monomialCurveForm_geometrically_irreducible d hp α⟩

/-- Incidence on the dual and primal quotient spaces, evaluated on arbitrary representatives. -/
theorem AGY_incidence_mk (a x : Fin 3 → F) (ha : a ≠ 0) (hx : x ≠ 0) :
    Projectivization.mk F x hx ∈ linePoints (Projectivization.mk F a ha) ↔
      a 0 * x 0 + a 1 * x 1 + a 2 * x 2 = 0 := by
  obtain ⟨r, hr⟩ := Projectivization.exists_smul_eq_mk_rep F a ha
  obtain ⟨s, hs⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  unfold linePoints
  simp only [Set.mem_setOf_eq, ← hr, ← hs, Units.smul_def, Pi.smul_apply, smul_eq_mul]
  rw [show (↑r * a 0) * (↑s * x 0) + (↑r * a 1) * (↑s * x 1) + (↑r * a 2) * (↑s * x 2) =
    ((r : F) * s) * (a 0 * x 0 + a 1 * x 1 + a 2 * x 2) by ring]
  simp [r.ne_zero, s.ne_zero]

/-- The rational zero set on the quotient gives the original equation on every representative. -/
theorem AGY_curve_mk {d : ℕ} (hd : 0 < d) (α : F) (x : Fin 3 → F) (hx : x ≠ 0) :
    Projectivization.mk F x hx ∈ curvePoints (pencilForm d α) ↔
      x 1 * x 2 ^ (d-1) = x 0 ^ d - α * x 2 ^ d := by
  obtain ⟨s, hs⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  obtain ⟨k, rfl⟩ : ∃ k, d = k+1 := ⟨d-1, by omega⟩
  unfold curvePoints pencilForm
  simp only [Set.mem_setOf_eq, ← hs, map_sub, map_mul, map_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Units.smul_def, Pi.smul_apply, smul_eq_mul, Nat.add_sub_cancel,
    mul_pow]
  rw [show (↑s ^ (k+1) * x 0 ^ (k+1) - α * (↑s ^ (k+1) * x 2 ^ (k+1))) -
      ↑s * x 1 * (↑s ^ k * x 2 ^ k) =
      (s : F) ^ (k+1) * (x 0 ^ (k+1) - α * x 2 ^ (k+1) - x 1 * x 2 ^ k) by ring]
  rw [mul_eq_zero, or_iff_right (pow_ne_zero _ s.ne_zero), sub_eq_zero, eq_comm]

private theorem vec_nonzero (x : Fin 3 → F) : x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
  constructor
  · contrapose!
    rintro ⟨h0,h1,h2⟩
    ext i
    fin_cases i <;> assumption
  · rintro h rfl
    simp at h

private theorem triple_nonzero {x y z : F} (h : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) :
    (![x,y,z] : Fin 3 → F) ≠ 0 := (vec_nonzero _).2 h

private theorem AGY_pencil_mk {d : ℕ} (hd : 0 < d) (S : Set F) (v : Fin 3 → F) (hv : v ≠ 0) :
    Projectivization.mk F v hv ∈ pencilPoints d S ↔
      ∃ α ∈ S, v 1 * v 2 ^ (d-1) = v 0 ^ d - α * v 2 ^ d := by
  simp only [pencilPoints, Set.mem_iUnion, AGY_curve_mk hd, Subtype.exists, exists_prop]

theorem AGY_blocking_iff {d : ℕ} (hd : 2 ≤ d) (S : Set F) :
    isBlocking (pencilPoints d S) ↔ ProjectiveBlocks d S := by
  have hp : 0 < d := by omega
  constructor
  · intro hb a b c hn
    obtain ⟨P, hL, hC⟩ := hb (Projectivization.mk F ![a,b,c] (triple_nonzero hn))
    induction P using Projectivization.ind with
    | h x hx =>
      obtain ⟨α, hα, he⟩ := (AGY_pencil_mk hp S x hx).1 hC
      exact ⟨α, hα, x 0, x 1, x 2, (vec_nonzero x).1 hx,
        (AGY_incidence_mk _ _ _ _).1 hL, he⟩
  · intro hb L
    induction L using Projectivization.ind with
    | h a ha =>
      obtain ⟨α,hα,x,y,z,hn,hL,hC⟩ := hb (a 0) (a 1) (a 2) ((vec_nonzero a).1 ha)
      let P := Projectivization.mk F ![x,y,z] (triple_nonzero hn)
      exact ⟨P, (AGY_incidence_mk a _ _ _).2 hL, (AGY_pencil_mk hp S _ _).2 ⟨α,hα,hC⟩⟩

theorem AGY_containsNoLine_iff {d : ℕ} (hd : 2 ≤ d) (S : Set F) :
    containsNoLine (pencilPoints d S) ↔ NoFullProjectiveLine d S := by
  have hp : 0 < d := by omega
  constructor
  · intro hb a b c hn
    have h := hb (Projectivization.mk F ![a,b,c] (triple_nonzero hn))
    obtain ⟨P, hL, hC⟩ := Set.not_subset.1 h
    induction P using Projectivization.ind with
    | h x hx =>
      refine ⟨x 0, x 1, x 2, (vec_nonzero x).1 hx, (AGY_incidence_mk _ _ _ _).1 hL, ?_⟩
      exact fun α hα he => hC ((AGY_pencil_mk hp S x hx).2 ⟨α,hα,he⟩)
  · intro hb L
    induction L using Projectivization.ind with
    | h a ha =>
      obtain ⟨x,y,z,hn,hL,hC⟩ := hb (a 0) (a 1) (a 2) ((vec_nonzero a).1 ha)
      apply Set.not_subset.2
      refine ⟨Projectivization.mk F ![x,y,z] (triple_nonzero hn), (AGY_incidence_mk _ _ _ _).2 hL, ?_⟩
      intro h
      obtain ⟨α,hα,he⟩ := (AGY_pencil_mk hp S _ _).1 h
      exact hC α hα he

theorem AGY_family_iff {d : ℕ} (hd : 2 ≤ d) (S : Finset F) :
    isBlockingFamily (fun _ : S => d) (fun α : S => pencilForm d (α : F)) ↔
      ProjectiveBlocks d (S : Set F) := by
  change ((∀ α : S, admissible d (pencilForm d (α : F))) ∧
    isBlocking (pencilPoints d (S : Set F))) ↔ _
  simp only [AGY_admissible hd, implies_true, true_and, AGY_blocking_iff hd]

theorem AGY_minimum_iff {d : ℕ} (hd : 2 ≤ d) (n : ℕ) :
    isPencilMinimum F d n ↔
    IsLeast {r : ℕ | ∃ S : Finset F, S.card = r ∧ ProjectiveBlocks d (S : Set F)} n := by
  simp only [isPencilMinimum, AGY_family_iff hd]

end BlockingCurves
