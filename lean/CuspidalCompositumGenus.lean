import CuspidalRootDegrees
import CuspidalRootGenus

/-! Castelnuovo–Severi on subfields of the product splitting field.
The classical inequality is supplied in dimension form. The factors of
each compositum, their degrees, and the two end fields are constructed. -/
namespace BlockingCurves.CuspidalRootTower
open CuspidalGeneral CuspidalTower IntermediateField FiniteDimensional
noncomputable section
universe u
variable {k M : Type u} [Field k] [Field M] [Algebra (RatFunc k) M]

def FormsFinite (E : IntermediateField (RatFunc k) M) : Prop :=
  FiniteDimensional k (fieldForms E)

/-- The classical compositum inequality for one-variable function fields
with full constant field k, as a bound on the rank of regular forms.
Our geometric application takes k algebraically closed. -/
def CastelnuovoSeveri (k M : Type u) [Field k] [Field M] [Algebra (RatFunc k) M] : Prop :=
  ∀ (A B E : IntermediateField (RatFunc k) M) (hA : A ≤ E) (hB : B ≤ E), E = A ⊔ B →
    FormsFinite A → FormsFinite B →
    Module.rank k (fieldForms E) ≤
      ((degreeOver hA * fieldGenus A + degreeOver hB * fieldGenus B +
        (degreeOver hA - 1) * (degreeOver hB - 1) : ℕ) : Cardinal)

private theorem rational_compositum_step (cs : CastelnuovoSeveri k M)
    (A B E : IntermediateField (RatFunc k) M) (hA : A ≤ E) (hB : B ≤ E) (join : E = A ⊔ B)
    (prev : FormsFinite A) (single : FormsFinite B) (zero : fieldGenus B = 0) :
    FormsFinite E ∧ fieldGenus E ≤ degreeOver hA * fieldGenus A +
      (degreeOver hA - 1) * (degreeOver hB - 1) := by
  have h := cs A B E hA hB join prev single
  rw [zero, Nat.mul_zero, Nat.add_zero] at h
  exact field_genus_of_rank_bound E h

variable {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0) (S : Finset k)
  (cs : CastelnuovoSeveri k (cuspCompositum d a S))

private theorem step_genus (i : Fin S.card) (j : Fin d)
    (previous : FormsFinite (stage hd ha S i j)) :
    FormsFinite (stage hd ha S i (j.val+1)) ∧
    fieldGenus (stage hd ha S i (j.val+1)) ≤
      relativeDegree hd ha S i j * fieldGenus (stage hd ha S i j) +
      (relativeDegree hd ha S i j - 1) * (overRootDegree hd ha S i j - 1) := by
  exact rational_compositum_step cs (stage hd ha S i j) (rootField hd ha S i j)
    (stage hd ha S i (j.val+1))
    (stage_le_next hd ha S i j) (rootField_le_next hd ha S i j)
    (stage_succ hd ha S i j) previous (single_root_forms_finite (sheet_mem_rootSet hd ha S i j))
    (single_root_genus (sheet_mem_rootSet hd ha S i j))

/-- Every visited stage has a finite-dimensional space of regular forms,
including when a sheet is already in the preceding field. -/
theorem stage_forms_finite {i j : ℕ} (hi : i < S.card) (hj : j ≤ d) :
    FormsFinite (stage hd ha S i j) := by
  have block (u : ℕ) (hu : u < S.card)
      (start : FormsFinite (stage hd ha S u 0)) :
      ∀ v ≤ d, FormsFinite (stage hd ha S u v) := by
    intro v
    induction v with
    | zero => exact fun _ => start
    | succ v ih =>
      intro hv
      exact (step_genus hd ha S cs ⟨u,hu⟩ ⟨v,by omega⟩ (ih (by omega))).1
  apply block i hi _ j hj
  clear hj
  induction i with
  | zero => rw [stage_base]; exact base_forms_finite
  | succ i ih =>
    have h : i < S.card := by omega
    rw [stage_glue hd ha S ⟨i,h⟩]
    exact block i h (ih h) d le_rfl

private def onStep {ell d : ℕ} (f : Fin ell → Fin d → ℕ) (i j : ℕ) : ℕ :=
  if h : i < ell ∧ j < d then f ⟨i,h.1⟩ ⟨j,h.2⟩ else 0

/-- The numerical tower used in the point-counting argument consists of
the finranks and genera of the specified intermediate fields. -/
def realizedTower : RootTower d S.card where
  degree i j := finrank (RatFunc k) (stage hd ha S i j)
  genus i j := fieldGenus (stage hd ha S i j)
  relative := onStep (relativeDegree hd ha S)
  overRoot := onStep (overRootDegree hd ha S)
  positive i _ j _ := stage_degree_pos hd ha S i j
  base_degree := (congrArg (fun E : IntermediateField (RatFunc k) (cuspCompositum d a S) =>
    finrank (RatFunc k) E) (stage_base hd ha S)).trans IntermediateField.finrank_bot
  base_genus := by change fieldGenus (stage hd ha S 0 0) = 0; rw [stage_base, base_genus]
  glue_degree i hi := congrArg (fun E : IntermediateField (RatFunc k) _ => finrank (RatFunc k) E)
    (stage_glue hd ha S ⟨i,hi⟩)
  glue_genus i hi := congrArg fieldGenus (stage_glue hd ha S ⟨i,hi⟩)
  tower_degree i hi j hj := by
    simpa only [onStep, dif_pos (And.intro hi hj)] using relative_degree_mul hd ha S ⟨i,hi⟩ ⟨j,hj⟩
  root_degree i hi j hj := by
    simpa only [onStep, dif_pos (And.intro hi hj)] using over_root_degree_mul hd ha S ⟨i,hi⟩ ⟨j,hj⟩
  residual_degree i hi j hj := by
    simpa only [onStep, dif_pos (And.intro hi hj)] using relative_degree_bound hd ha S ⟨i,hi⟩ ⟨j,hj⟩
  castelnuovo i hi j hj := by
    simpa only [onStep, dif_pos (And.intro hi hj)] using
      (step_genus hd ha S cs ⟨i,hi⟩ ⟨j,hj⟩ (stage_forms_finite hd ha S cs hi hj.le)).2

theorem terminal_degree : (realizedTower hd ha S cs).degree S.card 0 =
    finrank (RatFunc k) (cuspCompositum d a S) := by
  exact (congrArg (fun E : IntermediateField (RatFunc k) _ => finrank (RatFunc k) E)
    (stage_top hd ha S)).trans IntermediateField.finrank_top'

theorem terminal_genus : (realizedTower hd ha S cs).genus S.card 0 =
    ambientGenus k (cuspCompositum d a S) := by
  change fieldGenus (stage hd ha S S.card 0) = _
  rw [stage_top, fieldGenus_top]

/-- Uniform genus budget for the actual full splitting field. -/
theorem splitting_genus_budget :
    let H := finrank (RatFunc k) (cuspCompositum d a S)
    2 * ambientGenus k (cuspCompositum d a S) + 2*H ≤ S.card*(d-1)*H+2 := by
  simpa only [terminal_genus, terminal_degree] using
    genus_budget (by omega : 0 < d) (realizedTower hd ha S cs)

/-- A single threshold works for all slopes, sets of shifts and constant
fields. The degree and genus here refer to the full geometric cover. -/
theorem uniform_compositum_budget {d : ℕ} (hd : 3 ≤ d) {c : ℝ} (hc : 0 < c)
    (window : c * Real.log (d.factorial : ℝ) < 1/2) :
    ∀ᶠ q : ℝ in Filter.atTop, ∀ (k : Type u) [Field k] (a : k), a ≠ 0 →
      ∀ S : Finset k, (S.card : ℝ) ≤ c * Real.log q →
      CastelnuovoSeveri k (cuspCompositum d a S) →
      1 + (d : ℝ)*S.card^2 < q ∧
      (2*(S.card : ℝ)+1)*finrank (RatFunc k) (cuspCompositum d a S) <
        q+1-2*(ambientGenus k (cuspCompositum d a S) : ℝ)*Real.sqrt q := by
  filter_upwards [uniform_point_budget (by omega : 2 ≤ d) hc window] with q hq
  intro k _ a ha S hS cs
  simpa only [terminal_degree, terminal_genus] using hq _ hS (realizedTower hd ha S cs)

end
end BlockingCurves.CuspidalRootTower
