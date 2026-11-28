import CuspidalNontrivial
import StatementComparison

/-! The homogeneous cusp form, geometric irreducibility in all characteristics,
and the incidence comparison with projectivization. -/
namespace BlockingCurves.CuspidalGeneral

open AsgarliGhiocaYip Polynomial

variable {F : Type*} [Field F]

noncomputable def cuspForm (d : ℕ) (α : F) : Form F :=
  MvPolynomial.X 0 ^ d -
    (MvPolynomial.X 1 + MvPolynomial.C α * MvPolynomial.X 2)^(d-1) * MvPolynomial.X 2

theorem cuspForm_homogeneous {d : ℕ} (hd : 0 < d) (α : F) :
    (cuspForm d α).IsHomogeneous d := by
  apply (MvPolynomial.isHomogeneous_X_pow _ _).sub
  have linear := (MvPolynomial.isHomogeneous_X (R:=F) (σ:=Fin 3) 1).add
    (MvPolynomial.isHomogeneous_C_mul_X α 2)
  have form := (linear.pow (d-1)).mul (MvPolynomial.isHomogeneous_X (R:=F) 2)
  simpa only [one_mul,Nat.sub_add_cancel hd] using form

/-- Specialization Z=T, Y=1−αT takes the monic form to X^d−T. The latter
is Eisenstein at T over every coefficient field. -/
theorem cuspForm_irreducible {d : ℕ} (hd : 0 < d) (α : F) :
    Irreducible (cuspForm d α) := by
  classical
  let e := MvPolynomial.finSuccEquiv F 2
  let a : MvPolynomial (Fin 2) F :=
    (MvPolynomial.X 0 + MvPolynomial.C α * MvPolynomial.X 1)^(d-1)*MvPolynomial.X 1
  have mapped : e (cuspForm d α) = X^d-C a := by
    have hC : e (MvPolynomial.C α) = C (MvPolynomial.C α) := e.commutes α
    have hy : (1 : Fin 3) = (0 : Fin 2).succ := rfl
    have hz : (2 : Fin 3) = (1 : Fin 2).succ := rfl
    simp only [cuspForm,map_sub,map_add,map_mul,map_pow,hy,hz,hC]
    simp only [e,MvPolynomial.finSuccEquiv_X_zero,MvPolynomial.finSuccEquiv_X_succ,a,
      map_add,map_mul,map_pow]
  let φ := MvPolynomial.eval₂Hom (C : F →+* F[X]) ![1-C α*X,X]
  have ha : φ a = X := by simp [φ,a]
  have hir : Irreducible (e (cuspForm d α)) := by
    rw [mapped]
    apply Monic.irreducible_of_irreducible_map φ _ (monic_X_pow_sub_C _ hd.ne')
    simpa [Polynomial.map_sub,ha] using (irreducible_variable_binomial (K:=F) d hd)
  refine ⟨fun h => hir.not_unit (h.map e), ?_⟩
  intro b c he
  have h : e (cuspForm d α) = e b * e c := by rw [he,map_mul]
  exact (hir.isUnit_or_isUnit h).imp
    (fun hb => by simpa using hb.map e.symm) (fun hc => by simpa using hc.map e.symm)

theorem cuspForm_geometrically_irreducible {d : ℕ} (hd : 0<d) (α : F) :
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) (cuspForm d α)) := by
  simpa [cuspForm] using cuspForm_irreducible hd (algebraMap F (AlgebraicClosure F) α)

theorem cuspForm_admissible {d : ℕ} (hd : 2≤d) (α : F) : admissible d (cuspForm d α) := by
  have pos : 0<d := by omega
  have hom := cuspForm_homogeneous pos α
  exact ⟨hd,hom,hom.totalDegree (cuspForm_irreducible pos α).ne_zero,
    cuspForm_geometrically_irreducible pos α⟩

private theorem nonzero (x : Fin 3 → F) : x ≠ 0 ↔ x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
  constructor
  · contrapose!
    rintro ⟨a,b,c⟩
    ext i
    fin_cases i <;> assumption
  · rintro h rfl
    simp at h

theorem cuspForm_curve_mk {d : ℕ} (hd : 0<d) (α : F) (x : Fin 3 → F) (hx : x≠0) :
    Projectivization.mk F x hx ∈ curvePoints (cuspForm d α) ↔
      (x 1+α*x 2)^(d-1)*x 2=x 0^d := by
  obtain ⟨s,hs⟩ := Projectivization.exists_smul_eq_mk_rep F x hx
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hd.ne'
  unfold curvePoints cuspForm
  simp only [Set.mem_setOf_eq,← hs,map_sub,map_mul,map_pow,map_add,
    MvPolynomial.eval_C,MvPolynomial.eval_X,Units.smul_def,Pi.smul_apply,smul_eq_mul,
    Nat.succ_sub_one,sub_eq_zero]
  rw [show (s:F)*x 1 + α*((s:F)*x 2)=(s:F)*(x 1+α*x 2) by ring,mul_pow,mul_pow,
    show (s:F)^k*(x 1+α*x 2)^k*((s:F)*x 2)=(s:F)^k.succ*((x 1+α*x 2)^k*x 2) by
      rw [pow_succ];ring]
  exact (mul_right_inj' (pow_ne_zero _ s.ne_zero)).trans eq_comm

private theorem union_mk {d : ℕ} (hd : 0<d) (S : Set F) (x : Fin 3 → F) (hx : x≠0) :
    Projectivization.mk F x hx ∈ (⋃ α:S, curvePoints (cuspForm d (α:F))) ↔
      ∃ α∈S, (x 1+α*x 2)^(d-1)*x 2=x 0^d := by
  simp only [Set.mem_iUnion,cuspForm_curve_mk hd,Subtype.exists,exists_prop]

/-- The coordinate formulation used by the certificates gives the original
projective blocking-family definition, with all components admissible. -/
theorem cusp_family_iff {d : ℕ} (hd : 2≤d) (S : Finset F) :
    isBlockingFamily (fun _ : S => d) (fun α : S => cuspForm d (α : F)) ↔ Blocks d (S:Set F) := by
  have pos : 0<d := by omega
  simp only [isBlockingFamily,cuspForm_admissible hd,implies_true,true_and]
  constructor
  · intro hb a b c hn
    have nz : (![a,b,c] : Fin 3 → F) ≠ 0 := (nonzero _).2 hn
    obtain ⟨P,hl,hc⟩ := hb (Projectivization.mk F ![a,b,c] nz)
    induction P using Projectivization.ind with
    | h x hx =>
      obtain ⟨α,hα,he⟩ := (union_mk pos (S:Set F) x hx).1 hc
      exact ⟨α,hα,x 0,x 1,x 2,(nonzero _).1 hx,(AGY_incidence_mk _ _ _ _).1 hl,he⟩
  · intro hb line
    induction line using Projectivization.ind with
    | h a ha =>
      obtain ⟨α,hα,x,y,z,hn,hl,hc⟩ := hb (a 0) (a 1) (a 2) ((nonzero _).1 ha)
      have nz : (![x,y,z] : Fin 3 → F) ≠ 0 := (nonzero _).2 hn
      exact ⟨Projectivization.mk F ![x,y,z] nz,(AGY_incidence_mk _ _ _ _).2 hl,
        (union_mk pos (S:Set F) _ _).2 ⟨α,hα,hc⟩⟩

theorem cusp_containsNoLine_iff {d : ℕ} (hd : 0<d) (S : Set F) :
    containsNoLine (⋃ α:S, curvePoints (cuspForm d (α:F))) ↔ NoFullLine d S := by
  constructor
  · intro hn a b c h
    have nz : (![a,b,c] : Fin 3 → F) ≠ 0 := (nonzero _).2 h
    obtain ⟨P,hl,hc⟩ := Set.not_subset.1 (hn (Projectivization.mk F ![a,b,c] nz))
    induction P using Projectivization.ind with
    | h x hx =>
      refine ⟨x 0,x 1,x 2,(nonzero _).1 hx,(AGY_incidence_mk _ _ _ _).1 hl,?_⟩
      exact fun α hα he => hc ((union_mk hd S _ _).2 ⟨α,hα,he⟩)
  · intro hn line
    induction line using Projectivization.ind with
    | h a ha =>
      obtain ⟨x,y,z,h,hl,hc⟩ := hn (a 0) (a 1) (a 2) ((nonzero _).1 ha)
      have nz : (![x,y,z] : Fin 3 → F) ≠ 0 := (nonzero _).2 h
      apply Set.not_subset.2
      refine ⟨Projectivization.mk F ![x,y,z] nz,(AGY_incidence_mk _ _ _ _).2 hl,?_⟩
      intro mem
      obtain ⟨α,hα,he⟩ := (union_mk hd S _ _).1 mem
      exact hc α hα he

end BlockingCurves.CuspidalGeneral
