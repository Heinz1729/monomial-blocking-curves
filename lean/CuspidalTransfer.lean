import CubicPairCount
import CubicLogLog
import CubicSurfaceTrace

namespace BlockingCurves.Cuspidal

variable {F : Type*} [Field F]

/-- The projective union of the vertical translates of the affine cusp. -/
def Blocks (S : Set F) : Prop :=
  ∀ a b c : F, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ∃ α ∈ S, ∃ X Y Z : F, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧
      a*X+b*Y+c*Z=0 ∧ (Y+α*Z)^2*Z=X^3

theorem cusp_parametrization (x y : F) (h : y^2=x^3) :
    ∃ t : F, t^2=x ∧ t^3=y := by
  by_cases hx : x=0
  · subst x
    have hy : y=0 := by simpa using h
    exact ⟨0, by simp, by simp [hy]⟩
  · refine ⟨y/x, ?_, ?_⟩
    · field_simp [hx]
      linear_combination h
    · field_simp [hx]
      linear_combination y*h

theorem blocks_iff (S : Set F) : Blocks S ↔
    ∀ m b : F, ∃ t : F, t^3-m*t^2-b ∈ S := by
  constructor
  · intro hs m b
    obtain ⟨α,hα,X,Y,Z,hn,hl,hc⟩ := hs (-m) 1 (-b) (Or.inr (Or.inl one_ne_zero))
    have hz : Z ≠ 0 := by
      intro h
      subst Z
      have hx : X=0 := by simpa using hc.symm
      subst X
      have hy : Y=0 := by simpa using hl
      simp [hy] at hn
    have he : (Y/Z+α)^2=(X/Z)^3 := by
      field_simp [hz]
      linear_combination Z^2*hc
    obtain ⟨t,ht,ht'⟩ := cusp_parametrization _ _ he
    refine ⟨t,?_⟩
    convert hα using 1
    rw [ht,ht']
    field_simp [hz]
    linear_combination hl
  · intro hs a b c _
    by_cases hb : b=0
    · obtain ⟨t,ht⟩ := hs 0 0
      exact ⟨_,ht,0,1,0,Or.inr (Or.inl one_ne_zero),by simp [hb],by simp⟩
    · obtain ⟨t,ht⟩ := hs (-a/b) (-c/b)
      refine ⟨_,ht,t^2,(-a/b)*t^2+(-c/b),1,Or.inr (Or.inr one_ne_zero),?_,?_⟩
      · field_simp [hb]
        ring
      · ring

theorem graph_blocks_implies_cusp (S : Set F) (h3 : (3:F) ≠ 0)
    (h : ProjectiveBlocks 3 S) : Blocks S := by
  apply (blocks_iff S).2
  intro m b
  let u := m/3
  have hm : m=3*u := by dsimp [u]; field_simp
  obtain ⟨x,hx⟩ := (projectiveBlocks_iff_graphHits (by decide : 2≤3) S).1 h
    (3*u^2) (b+2*u^3)
  exact ⟨x+u, by convert hx using 1; rw [hm]; ring⟩

variable [Fintype F] [DecidableEq F]

/-- Actual nonhorizontal affine lines omitted by the cusp family. -/
def missedLines (S : Finset F) : Finset (F × F) :=
  Finset.univ.filter fun P => P.1 ≠ 0 ∧ ∀ t : F, t^3-P.1*t^2-P.2 ∉ S

private def chart (P : F × F) : F × F := (P.2+4*(P.1/3)^3,P.2)

private theorem chart_mem (S : Finset F) (h2 : (2:F)≠0) (h3 : (3:F)≠0)
    (m b : F) : chart (m,b) ∈ CubicPairCount.escapePairs S ↔ (m,b) ∈ missedLines S := by
  let u := m/3
  have hm : m=3*u := by dsimp [u]; field_simp
  have h4 : (4:F) ≠ 0 := by rw [show (4:F)=2*2 by ring]; exact mul_ne_zero h2 h2
  change (b+4*u^3,b) ∈ _ ↔ _
  simp only [CubicPairCount.escapePairs,missedLines,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hu : u=0
  · simp [hu,hm]
  have hdiff : b+4*u^3-b ≠ 0 := by simpa using mul_ne_zero h4 (pow_ne_zero 3 hu)
  have hid (k a : F) :
      k^3-3*k=CubicPairCount.parameter (b+4*u^3) b a ↔
      (u*(k+1))^3-m*(u*(k+1))^2-b=a := by
    rw [CubicPairCount.parameter, eq_div_iff hdiff, hm]
    constructor <;> intro h
    · apply mul_left_cancel₀ h4
      linear_combination h
    · linear_combination 4*h
  constructor
  · rintro ⟨_,_,h⟩
    refine ⟨by rw [hm]; exact mul_ne_zero h3 hu, ?_⟩
    intro t ht
    apply h _ ht (t/u-1)
    apply (hid _ _).2
    rw [show u*(t/u-1+1)=t by field_simp [hu]]
  · rintro ⟨_,h⟩
    refine ⟨sub_ne_zero.mp hdiff, ?_, ?_⟩
    · intro a ha
      constructor
      · intro e
        apply h (2*u)
        convert ha using 1
        rw [hm]
        linear_combination -e
      · intro e
        apply h 0
        convert ha using 1
        simp [e]
    · intro a ha k e
      apply h (u*(k+1))
      rwa [(hid _ _).1 e]

theorem missedLines_card (S : Finset F) (h2 : (2:F) ≠ 0) (h3 : (3:F) ≠ 0)
    (hq : Fintype.card F % 3=2) :
    (missedLines S).card=CubicPairCount.escapeCount S := by
  have surj := CubicSlope.cube_surjective (F:=F) hq
  have inj := (Finite.injective_iff_surjective).2 surj
  have h4 : (4:F) ≠ 0 := by rw [show (4:F)=2*2 by ring]; exact mul_ne_zero h2 h2
  apply Finset.card_bij (fun P _ => chart P)
  · rintro ⟨m,b⟩ h
    exact (chart_mem S h2 h3 m b).2 h
  · rintro ⟨m,b⟩ _ ⟨n,c⟩ _ h
    have bc : b=c := congrArg Prod.snd h
    subst c
    have fst := congrArg Prod.fst h
    change b+4*(m/3)^3=b+4*(n/3)^3 at fst
    have powEq := mul_left_cancel₀ h4 (add_left_cancel fst)
    have eq := inj powEq
    change m/3=n/3 at eq
    field_simp [h3] at eq
    exact Prod.ext eq rfl
  · rintro ⟨v,w⟩ h
    obtain ⟨u,hu⟩ := surj ((v-w)/4)
    change u^3=(v-w)/4 at hu
    have eq : chart (3*u,w)=(v,w) := by
      refine Prod.ext ?_ rfl
      change w+4*(3*u/3)^3=v
      rw [show 3*u/3=u by field_simp,hu]
      field_simp [h4]
    exact ⟨(3*u,w),(chart_mem S h2 h3 _ _).1 (eq.symm ▸ h),eq⟩

theorem lower_of_trace (S : Finset F) (h2 : (2:F)≠0) (h3 : (3:F)≠0)
    (hq : Fintype.card F % 3=2) (hlarge : 16 ≤ (Fintype.card F : ℝ))
    (ht : CubicAsymptotics.traceDeviation (Fintype.card F) S.card (CubicPairCount.escapeCount S))
    (hs : Blocks (S : Set F)) :
    (Real.log (Fintype.card F)-2*Real.log (Real.log (Fintype.card F)))/Real.log 4-5
      < (S.card : ℝ) := by
  have hz : missedLines S=∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    rintro ⟨m,b⟩ h
    obtain ⟨t,ht'⟩ := (blocks_iff _).1 hs m b
    exact (Finset.mem_filter.mp h).2.2 t ht'
  rw [← missedLines_card S h2 h3 hq,hz,Finset.card_empty] at ht
  exact CubicAsymptotics.cubic_lower_of_trace _ _ hlarge ht

/-- A witness for the graph minimum gives an actual projective cusp cover. -/
theorem cover_of_minimum {n : ℕ} (hn : AsgarliGhiocaYip.isPencilMinimum F 3 n)
    (h3 : (3:F)≠0) : ∃ S : Finset F, S.card=n ∧ Blocks (S : Set F) := by
  obtain ⟨S,hn',hs⟩ := ((AGY_minimum_iff (by decide : 2 ≤ 3) _).1 hn).1
  exact ⟨S,hn',graph_blocks_implies_cusp _ h3 hs⟩

theorem upper_finite_range (hq : Fintype.card F % 3=2)
    (hL : Real.log (Fintype.card F) ≤ (3:ℝ)^9) :
    ∃ S : Finset F, Blocks (S : Set F) ∧ (S.card : ℝ) ≤
      (2*Real.log (Fintype.card F)-Real.log (Real.log (Fintype.card F)))/Real.log 3+17 := by
  obtain ⟨n,hn,hsize⟩ := CubicLogLog.minimum_upper_finite_range hq hL
  obtain ⟨S,hcard,hs⟩ := cover_of_minimum hn (CubicLogLog.three_ne_zero hq)
  exact ⟨S,hs,hcard ▸ hsize⟩

/-- The original surface laws control the exact nonhorizontal cusp-line count. -/
theorem trace_on_missed_lines (S : Finset F) (h2 : (2:F)≠0)
    (hq : Fintype.card F % 3=2) (H : CubicSurfaceTrace.SurfaceSpectrum S)
    (law : CubicSurfaceTrace.SurfaceLaws S H) :
    CubicAsymptotics.traceDeviation (Fintype.card F) S.card (missedLines S).card := by
  rw [missedLines_card S h2 (CubicLogLog.three_ne_zero hq) hq]
  exact CubicSurfaceTrace.trace_deviation_of_spectra S H law

end BlockingCurves.Cuspidal
