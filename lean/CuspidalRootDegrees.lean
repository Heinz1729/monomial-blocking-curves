import CuspidalRootTower
import CuspidalTowerBudget

/-! The relative degrees in the root-by-root tower of the joint splitting field.
At each step the previous roots remove distinct linear factors. The degree over
the parameter field of a single root is exactly the original polynomial degree. -/

namespace BlockingCurves.CuspidalRootTower

open Polynomial IntermediateField FiniteDimensional CuspidalGeneral

section Residual

variable {B M : Type*} [Field B] [Field M] [Algebra B M]

/-- Work over the field of the current stage. Previous roots remain distinct
as elements of that field, including when the next root is already there. -/
private theorem ordered_root_bound {d : ℕ} (P : B[X]) (hm : P.Monic)
    (xs : Fin d → M) (hinj : Function.Injective xs)
    (hroot : ∀ t, aeval (xs t) P = 0) (V : IntermediateField B M)
    (j : Fin d) (hmem : ∀ t : Fin d, t.val < j.val → xs t ∈ V) :
    finrank V (adjoin V ({xs j} : Set M)) + j.val ≤ P.natDegree := by
  classical
  let ix : Fin j.val → Fin d := fun t => ⟨t.val, t.isLt.trans j.isLt⟩
  let past : Fin j.val ↪ V :=
    { toFun := fun t => ⟨xs (ix t), hmem (ix t) t.isLt⟩
      inj' := by
        intro s t eq
        apply Fin.ext
        exact congrArg (fun z : Fin d => z.val) (hinj (congrArg Subtype.val eq)) }
  let Q := P.map (algebraMap B V)
  have bound := CuspidalTower.remaining_root_degree Q (hm.map _) (xs j)
    (by simpa only [Q, aeval_map_algebraMap] using hroot j)
    (Finset.univ.map past) (by
      intro z hz
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hz
      apply (algebraMap V M).injective
      rw [map_zero]
      change algebraMap V M (Q.eval (past t)) = 0
      rw [eval_map_algebraMap]
      change V.val (aeval (past t) P) = 0
      rw [← aeval_algHom_apply V.val]
      exact hroot (ix t)) (by
      intro z hz eq
      obtain ⟨t, _, rfl⟩ := Finset.mem_map.mp hz
      have e : j = ix t := hinj eq
      exact (Nat.ne_of_lt t.isLt) (congrArg Fin.val e.symm))
  simpa [Q] using bound

private theorem restrict_simple (V : IntermediateField B M) (x : M) :
    (adjoin V ({x} : Set M)).restrictScalars B = V ⊔ adjoin B ({x} : Set M) := by
  rw [restrictScalars_adjoin]
  calc
    _ = adjoin B (V : Set M) ⊔ adjoin B ({x} : Set M) := IntermediateField.gc.l_sup
    _ = _ := by rw [adjoin_self]

/-- The relative field degree of a specified inclusion of intermediate fields. -/
noncomputable def degreeOver {V W : IntermediateField B M} (h : V ≤ W) : ℕ :=
  finrank V (extendScalars h)

private theorem degreeOver_mul {V W : IntermediateField B M} (h : V ≤ W) :
    finrank B W = finrank B V * degreeOver h := by
  change finrank B ((extendScalars h).restrictScalars B) = finrank B V * finrank V _
  exact (finrank_mul_finrank B V (extendScalars h)).symm

end Residual

variable {k : Type*} [Field k] {d : ℕ} (hd : 3 ≤ d) {a : k} (ha : a ≠ 0)
  (S : Finset k) (i : Fin S.card) (j : Fin d)

/-- Field of just the chosen sheet (together with the rational parameter). -/
noncomputable def rootField : IntermediateField (RatFunc k) (cuspCompositum d a S) :=
  adjoin (RatFunc k) ({sheet hd ha S i j} : Set _)

theorem stage_le_next : stage hd ha S i j ≤ stage hd ha S i (j.val+1) := by
  rw [stage_succ]; exact le_sup_left

theorem rootField_le_next : rootField hd ha S i j ≤ stage hd ha S i (j.val+1) := by
  rw [stage_succ]; exact le_sup_right

/-- Both relative degrees in the Castelnuovo–Severi step use the same target field. -/
noncomputable def relativeDegree : ℕ := degreeOver (stage_le_next hd ha S i j)

noncomputable def overRootDegree : ℕ := degreeOver (rootField_le_next hd ha S i j)

theorem relative_eq_degreeOver (h : stage hd ha S i j ≤ stage hd ha S i (j.val+1)) :
    relativeDegree hd ha S i j = degreeOver h := rfl

theorem overRoot_eq_degreeOver (h : rootField hd ha S i j ≤ stage hd ha S i (j.val+1)) :
    overRootDegree hd ha S i j = degreeOver h := rfl

private theorem step_adjoin :
    extendScalars (stage_le_next hd ha S i j) =
      adjoin (stage hd ha S i j) ({sheet hd ha S i j} : Set _) := by
  apply restrictScalars_injective (RatFunc k)
  rw [extendScalars_restrictScalars, restrict_simple, stage_succ]

private theorem coordinate_monic (u : k) : (cuspCoordinate d a u).Monic :=
  integralFibre_monic (by omega : 2 ≤ d) _ _

/-- The exact relative degree is the minimal-polynomial degree at this stage. -/
theorem relative_eq_minpoly_degree :
    relativeDegree hd ha S i j =
      (minpoly (stage hd ha S i j) (sheet hd ha S i j)).natDegree := by
  unfold relativeDegree degreeOver
  rw [step_adjoin, adjoin.finrank]
  exact ⟨(cuspCoordinate d a (shift S i)).map (algebraMap (RatFunc k) (stage hd ha S i j)),
    (coordinate_monic hd (a:=a) _).map _, by
      exact (aeval_map_algebraMap (stage hd ha S i j) _ _).trans (sheet_aeval hd ha S i j)⟩

theorem relative_degree_bound : relativeDegree hd ha S i j + j.val ≤ d := by
  unfold relativeDegree degreeOver
  rw [step_adjoin]
  exact (ordered_root_bound _ (coordinate_monic hd _) _ (sheet_injective hd ha S i)
    (sheet_aeval hd ha S i) _ j (fun t ht => sheet_mem_stage hd ha S i t ht)).trans
      (cuspCoordinate_natDegree (by omega : 2 ≤ d) a (shift S i)).le

theorem stage_degree_pos (u v : ℕ) : 0 < finrank (RatFunc k) (stage hd ha S u v) :=
  finrank_pos

theorem relative_degree_mul :
    finrank (RatFunc k) (stage hd ha S i (j.val+1)) =
      relativeDegree hd ha S i j * finrank (RatFunc k) (stage hd ha S i j) := by
  rw [Nat.mul_comm]
  exact degreeOver_mul (stage_le_next hd ha S i j)

theorem relative_degree_pos : 0 < relativeDegree hd ha S i j := by
  have hp := stage_degree_pos hd ha S i (j.val+1)
  rw [relative_degree_mul hd ha S i j] at hp
  by_contra! hz
  simp [Nat.eq_zero_of_le_zero hz] at hp

/-- The last sheet of each polynomial already belongs to the preceding stage. -/
theorem last_sheet_degree_one (last : j.val+1 = d) : relativeDegree hd ha S i j = 1 := by
  have pos := relative_degree_pos hd ha S i j
  have bound := relative_degree_bound hd ha S i j
  omega

/-- Generic irreducibility gives the full single-root degree in every characteristic. -/
theorem single_root_degree : finrank (RatFunc k) (rootField hd ha S i j) = d := by
  have hm := coordinate_monic hd (a:=a) (shift S i)
  have hx := sheet_aeval hd ha S i j
  unfold rootField
  rw [adjoin.finrank (show IsIntegral (RatFunc k) (sheet hd ha S i j) from ⟨_,hm,hx⟩),
    ← minpoly.eq_of_irreducible_of_monic (cuspCoordinate_irreducible (by omega) _ _) hx hm]
  exact cuspCoordinate_natDegree (by omega) _ _

/-- At the very first step generic irreducibility forces equality in the
residual bound. Subsequent coordinates may intersect earlier splitting fields. -/
theorem first_sheet_degree (hi : i.val = 0) (hj : j.val = 0) :
    relativeDegree hd ha S i j = d := by
  let rank := fun V : IntermediateField (RatFunc k) (cuspCompositum d a S) => finrank (RatFunc k) V
  have base : stage hd ha S i j = ⊥ := by rw [hi, hj, stage_base]
  have next : stage hd ha S i (j.val+1) = rootField hd ha S i j := by
    rw [stage_succ, base, bot_sup_eq]; rfl
  have one : rank (stage hd ha S i j) = 1 :=
    (congrArg rank base).trans IntermediateField.finrank_bot
  have full : rank (stage hd ha S i (j.val+1)) = d :=
    (congrArg rank next).trans (single_root_degree hd ha S i j)
  have mul := relative_degree_mul hd ha S i j
  change rank _ = relativeDegree hd ha S i j * rank _ at mul
  rw [one, full, Nat.mul_one] at mul
  exact mul.symm

theorem over_root_degree_mul :
    finrank (RatFunc k) (stage hd ha S i (j.val+1)) = d * overRootDegree hd ha S i j := by
  exact (degreeOver_mul (rootField_le_next hd ha S i j)).trans
    (congrArg (· * overRootDegree hd ha S i j) (single_root_degree hd ha S i j))

/-- The field degree of the whole compositum has a factorial bound, without
any hypothesis on genera, local ramification, or Frobenius. -/
theorem splitting_degree_bound :
    finrank (RatFunc k) (cuspCompositum d a S) ≤ d.factorial ^ S.card := by
  let rank := fun V : IntermediateField (RatFunc k) (cuspCompositum d a S) => finrank (RatFunc k) V
  have bound := CuspidalTower.degree_budget_of_steps (d:=d) (ell:=S.card)
    (fun u v => rank (stage hd ha S u v))
    ((congrArg rank (stage_base hd ha S)).trans IntermediateField.finrank_bot)
    (fun u hu => congrArg rank (stage_glue hd ha S ⟨u, hu⟩))
    (fun u hu v hv => by
      let u' : Fin S.card := ⟨u, hu⟩
      let v' : Fin d := ⟨v, hv⟩
      have e := relative_degree_bound hd ha S u' v'
      apply (relative_degree_mul hd ha S u' v').le.trans
      exact Nat.mul_le_mul_right _ (show relativeDegree hd ha S u' v' ≤ d-v by
        change relativeDegree hd ha S u' v' + v ≤ d at e
        omega))
  have terminal := (congrArg rank (stage_top hd ha S)).trans IntermediateField.finrank_top'
  exact terminal.symm.le.trans bound

end BlockingCurves.CuspidalRootTower
