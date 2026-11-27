import PhaseCommonVariable

/-! Slopes and complete rational fibres for arbitrary tables of ground-field coefficients. -/
namespace BlockingCurves.PiecewiseFibres

open Finset NormPencil ExtensionPhase

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def branch (a : E) (c : F) (x : E) : E :=
  algebraMap F E c * x ^ Fintype.card F - a*x

/-- Lift any nonzero norm target. At this slope a coefficient branch is
injective exactly when its nth power differs from the target. -/
theorem slope_of_norm {n : ℕ} (hn : 0 < n) (size : Fintype.card E = Fintype.card F^n)
    (v : F) (hv : v ≠ 0) :
    ∃ a : Eˣ, ∀ c : F, c ≠ 0 →
      (Function.Injective (branch (a:E) c) ↔ c^n ≠ v) := by
  obtain ⟨a,ha⟩ := norm_power_surjective hn size v
  have ha0 : a ≠ 0 := by
    intro eq
    rw [eq,zero_pow (normExponent_pos Fintype.card_pos hn).ne'] at ha
    exact hv ((map_eq_zero _).mp ha.symm)
  refine ⟨Units.mk0 a ha0,fun c hc => ?_⟩
  let z := Units.mk0 (algebraMap F E c) ((map_ne_zero _).mpr hc)
  have hi := branch_injective_iff_norm_ne hn size z (Units.mk0 a ha0)
  change Function.Injective (branch a c) ↔
    a^normExponent (Fintype.card F) n ≠ (algebraMap F E c)^normExponent (Fintype.card F) n at hi
  rw [ha,← map_pow,scalar_norm_power] at hi
  exact hi.trans ⟨fun h e => h (congrArg (algebraMap F E) e.symm),fun h e => h ((algebraMap F E).injective e).symm⟩

/-- Either avoid all coefficient norms, or choose a norm met by exactly one
branch. The exceptional case is possible only when the base field has m+1 elements. -/
theorem good_slope {m n : ℕ} (hn : 0 < n) (size : Fintype.card E = Fintype.card F^n)
    (C : Finset F) (nonzero : ∀ c ∈ C, c ≠ 0) (few : C.card ≤ m)
    (index : m ≤ Fintype.card F-1) :
    ∃ a : Eˣ, (∀ c ∈ C, Function.Injective (branch (a:E) c)) ∨
      (Fintype.card F = m+1 ∧ ∃ d ∈ C, ¬Function.Injective (branch (a:E) d) ∧
        ∀ c ∈ C, c ≠ d → Function.Injective (branch (a:E) c)) := by
  classical
  let V := C.image (fun c => c^n)
  let U := (univ : Finset F).erase 0
  have sub : V ⊆ U := by
    intro x hx
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hx
    exact mem_erase.mpr ⟨pow_ne_zero _ (nonzero c hc),mem_univ _⟩
  by_cases cov : U ⊆ V
  · have eq : V = U := Finset.Subset.antisymm sub cov
    have cU : U.card = Fintype.card F-1 := by simp [U]
    have cle : V.card ≤ C.card := card_image_le
    have hs : 1 < Fintype.card F := Fintype.one_lt_card
    have hcard : V.card = C.card := by rw [eq,cU] at cle ⊢; omega
    have all : Set.InjOn (fun c : F => c^n) C := injOn_of_card_image_eq hcard
    have one : (1:F) ∈ V := cov (mem_erase.mpr ⟨one_ne_zero, mem_univ _⟩)
    obtain ⟨d,hd,hdv⟩ := mem_image.mp one
    obtain ⟨a,ha⟩ := slope_of_norm hn size 1 one_ne_zero
    refine ⟨a,Or.inr ⟨?_,d,hd,fun hi => ((ha d (nonzero d hd)).mp hi) hdv,?_⟩⟩
    · rw [eq,cU] at cle
      omega
    · intro c hc ne
      exact (ha c (nonzero c hc)).mpr (fun h => ne (all hc hd (h.trans hdv.symm)))
  · obtain ⟨v,hU,hV⟩ := Finset.not_subset.mp cov
    obtain ⟨a,ha⟩ := slope_of_norm hn size v (mem_erase.mp hU).1
    exact ⟨a,Or.inl (fun c hc => (ha c (nonzero c hc)).mpr (fun h =>
      hV (mem_image.mpr ⟨c,hc,h⟩)))⟩

/-- The sigma index is over distinct coefficients and contains each rational
preimage, even if the fibre is empty or has the full ground-field cardinality. -/
abbrev Candidate (C : Finset F) (a : E) (S : Finset E) :=
  (α : S) × (c : C) × {u : E // branch a c.val u = α.val}

theorem candidate_card (C : Finset F) (a : E) (S : Finset E) :
    Nat.card (Candidate C a S) =
      ∑ α ∈ S, ∑ c ∈ C, Nat.card {u : E // branch a c u = α} := by
  classical
  simp only [Candidate,Nat.card_eq_fintype_card,Fintype.card_sigma]
  change (∑ α : S, ∑ c : C, Fintype.card {u : E // branch a c.val u = α.val}) = _
  rw [← Finset.sum_coe_sort S (fun α => ∑ c ∈ C, Fintype.card {u : E // branch a c u = α})]
  exact Finset.sum_congr rfl (fun α _ =>
    Finset.sum_coe_sort C (fun c => Fintype.card {u : E // branch a c u = α.val}))

/-- All exceptional fibres are retained at the very same slope, for every S. -/
theorem budget_at_slope {m n : ℕ} (hn : 0 < n) (size : Fintype.card E = Fintype.card F^n)
    (C : Finset F) (nonzero : ∀ c ∈ C, c ≠ 0) (few : C.card ≤ m)
    (a : Eˣ) (choice : (∀ c ∈ C, Function.Injective (branch (a:E) c)) ∨
      (Fintype.card F = m+1 ∧ ∃ d ∈ C, ¬Function.Injective (branch (a:E) d) ∧
        ∀ c ∈ C, c ≠ d → Function.Injective (branch (a:E) c))) (S : Finset E) :
    Nat.card (Candidate C (a:E) S) ≤ 2*m*S.card := by
  classical
  let sizeAt (α : E) (c : F) := Nat.card {u : E // branch (a:E) c u = α}
  have easy {c : F} (inj : Function.Injective (branch (a:E) c)) (α : E) :
      sizeAt α c ≤ 1 := by
    haveI : Subsingleton {u : E // branch (a:E) c u = α} :=
      ⟨fun x y => Subtype.ext (inj (x.2.trans y.2.symm))⟩
    change Nat.card _ ≤ 1
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have per (α : E) : ∑ c ∈ C, sizeAt α c ≤ 2*m := by
    rcases choice with all | ⟨hs,d,hd,bad,other⟩
    · have h := Finset.sum_le_sum (s := C) (g := fun _ => 1) (fun c hc => easy (all c hc) α)
      simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
      exact h.trans (by omega)
    · let dz := Units.mk0 (algebraMap F E d) ((map_ne_zero _).mpr (nonzero d hd))
      have h := branch_injective_iff_norm_ne hn size dz a
      have normEq := not_not.mp (mt h.2 bad)
      have hc := singular_fibre_card hn size dz a α normEq
      change sizeAt α d = 0 ∨ sizeAt α d = Fintype.card F at hc
      have hother := Finset.sum_le_sum (s := C.erase d) (g := fun _ => 1)
        (fun c hc => easy (other c (mem_erase.mp hc).2 (mem_erase.mp hc).1) α)
      simp only [Finset.sum_const,smul_eq_mul,mul_one,card_erase_of_mem hd] at hother
      rw [← Finset.sum_erase_add _ _ hd]
      have hpos := card_pos.mpr ⟨d,hd⟩
      have hdle : sizeAt α d ≤ Fintype.card F := by rcases hc with hc | hc <;> omega
      exact (Nat.add_le_add hother hdle).trans (by omega)
  rw [candidate_card]
  have h := Finset.sum_le_sum (s := S) (g := fun _ => 2*m) (fun α _ => per α)
  simpa only [Finset.sum_const,smul_eq_mul,Nat.mul_comm S.card] using h

theorem rational_candidate_budget {m n : ℕ} (hn : 0 < n) (size : Fintype.card E = Fintype.card F^n)
    (C : Finset F) (nonzero : ∀ c ∈ C, c ≠ 0) (few : C.card ≤ m) (index : m ≤ Fintype.card F-1) :
    ∃ a : Eˣ, ∀ S : Finset E, Nat.card (Candidate C (a:E) S) ≤ 2*m*S.card := by
  obtain ⟨a,ha⟩ := good_slope hn size C nonzero few index
  exact ⟨a,budget_at_slope hn size C nonzero few a ha⟩

/-- The finite image of the coefficient table on the labels actually attained
by nonzero inputs; this omits any value supplied only at zero. -/
noncomputable def coefficients [DecidableEq E] [DecidableEq F] (table : E → F) (m : ℕ) : Finset F :=
  univ.image (fun x : Eˣ => table ((x:E)^((Fintype.card E-1)/m)))

theorem mem_coefficients [DecidableEq E] [DecidableEq F] (table : E → F) (m : ℕ) (x : Eˣ) :
    table ((x:E)^((Fintype.card E-1)/m)) ∈ coefficients table m :=
  mem_image.mpr ⟨x,mem_univ x,rfl⟩

theorem coefficients_card [DecidableEq E] [DecidableEq F] {m : ℕ} (hm : 0 < m)
    (dvd : m ∣ Fintype.card E-1) (table : E → F) : (coefficients table m).card ≤ m := by
  classical
  let k := (Fintype.card E-1)/m
  let U := (univ : Finset Eˣ).filter (fun z => z^m=1)
  have sub : coefficients table m ⊆ U.image (fun z : Eˣ => table (z:E)) := by
    intro c hc
    unfold coefficients at hc
    obtain ⟨u,_,rfl⟩ := mem_image.mp hc
    have eq : (u^k)^m=1 := by
      rw [← pow_mul,Nat.div_mul_cancel dvd,← Fintype.card_units]
      exact pow_card_eq_one
    exact mem_image.mpr ⟨u^k,mem_filter.mpr ⟨mem_univ _,eq⟩,rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (IsCyclic.card_pow_eq_one_le hm))

end BlockingCurves.PiecewiseFibres
