import CuspidalRootInertia

/-! The excluded intercepts and the arithmetic Frobenius permutation on
each remaining cusp fibre, including in wild characteristic. -/
namespace BlockingCurves.CuspidalGeneral

open Finset Polynomial PencilSampling
noncomputable section

variable {F : Type*} [Field F]

theorem lineFibre_natDegree {d : ℕ} (hd : 2 ≤ d) (a v : F) :
    (lineFibre d a v).natDegree = d := by
  have small : (C a * X^(d-1) + C v : F[X]).natDegree ≤ d-1 := by
    apply natDegree_add_le_of_degree_le
    · simpa using natDegree_C_mul_le a ((X:F[X])^(d-1))
    · simp
  rw [lineFibre,natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X_pow]; omega),
    natDegree_X_pow]

/-- The finite fibre away from both critical values has d distinct geometric roots. -/
theorem lineFibre_separable {d : ℕ} (hd : 3 ≤ d) {a v : F} (ha : a ≠ 0)
    (hzero : v ≠ 0) (hextra : v ≠ extraCritical d a) : (lineFibre d a v).Separable := by
  by_contra hn
  have hnonzero : lineFibre d a v ≠ 0 := (integralFibre_monic (by omega) a v).ne_zero
  obtain ⟨z,hz,hz'⟩ := exists_common_root_of_not_separable hnonzero hn
  let f := algebraMap F (AlgebraicClosure F)
  have hvalue : z^d - f a*z^(d-1) = f v := by
    simp only [lineFibre,map_sub,map_add,map_mul,map_pow,aeval_X,aeval_C] at hz
    linear_combination hz
  have hcrit : ((X^d-C (f a)*X^(d-1)):(AlgebraicClosure F)[X]).derivative.eval z = 0 := by
    rw [aeval_def,←eval_map,←derivative_map] at hz'
    simpa only [lineFibre,Polynomial.map_sub,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,derivative_sub,derivative_add,
      derivative_C,add_zero,f] using hz'
  have h := critical_value_cases hd (f a) z ((_root_.map_ne_zero f).mpr ha) hcrit
  rcases h with h | h
  · exact hzero ((_root_.map_eq_zero f).mp (hvalue.symm.trans h))
  · apply hextra
    apply f.injective
    simpa only [extraCritical,map_mul,map_sub,map_pow,map_div₀,map_natCast] using
      hvalue.symm.trans h

variable [DecidableEq F]

/-- Infinity and the translates of the two possible finite critical values. -/
def excludedBranches (d : ℕ) (a : F) (S : Finset F) : Finset (Option F) :=
  insert none ((S.image fun α => some (-α)) ∪ (S.image fun α => some (extraCritical d a - α)))

theorem excludedBranches_card (d : ℕ) (a : F) (S : Finset F) :
    (excludedBranches d a S).card ≤ 2*S.card+1 := by
  apply (card_insert_le _ _).trans
  have h := card_union_le (S.image fun α => some (-α)) (S.image fun α => some (extraCritical d a - α))
  have h₁ := card_image_le (f := fun α : F => some (-α)) (s := S)
  have h₂ := card_image_le (f := fun α : F => some (extraCritical d a - α)) (s := S)
  omega

/-- Every coordinate is separable off the explicit translated branch values. -/
theorem unexcluded_separable {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0)
    (S : Finset F) {b : F} (hb : some b ∉ excludedBranches d a S) (α : S) :
    (lineFibre d a (b+α.val)).Separable := by
  have avoid₀ : b ≠ -α.val := by
    rintro rfl
    exact hb (Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image_of_mem _ α.property)))
  have avoid₁ : b ≠ extraCritical d a - α.val := by
    rintro rfl
    exact hb (Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ α.property)))
  exact lineFibre_separable hd ha (fun h => avoid₀ (by linear_combination h))
    (fun h => avoid₁ (by linear_combination h))

variable [Fintype F]

/-- The q-power permutation on the actual geometric sheets of each unexcluded rational fibre. -/
def regularFibreAction {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F) {b : F}
    (hb : some b ∉ excludedBranches d a S) (α : S) : FibreAction (lineFibre d a (b+α.val)) d := by
  exact fibreAction (unexcluded_separable hd ha S hb α) (lineFibre_natDegree (by omega) _ _)

/-- A conjugacy comparison can always be realized as equality by relabelling the same roots. -/
theorem relabel_conjugate {P : F[X]} {d : ℕ} (A : FibreAction P d)
    {γ : Equiv.Perm (Fin d)} (h : IsConj A.perm γ) : ∃ B : FibreAction P d, B.perm = γ := by
  obtain ⟨s,rfl⟩ := isConj_iff.mp h
  refine ⟨⟨s.symm.trans A.label,s * A.perm * s⁻¹,?_⟩,rfl⟩
  intro j
  simpa [Equiv.Perm.mul_apply] using A.frobenius (s.symm j)

/-- Construct twist point data from a point bound, the fibre-degree bound and
the usual unramified specialization statement up to conjugacy. -/
def TwistPointData.ofConjugacy {d : ℕ} (hd : 3 ≤ d) {a : F} (ha : a ≠ 0) (S : Finset F)
    (γ : S → Equiv.Perm (Fin d)) (points genus degree : ℕ) (projection : Fin points → Option F)
    (hasse_weil : (Fintype.card F:ℝ)+1-2*genus*Real.sqrt (Fintype.card F) ≤ points)
    (fibre_degree : ∀ b, (univ.filter fun p => projection p = b).card ≤ degree)
    (specialization : ∀ p b, projection p = some b → ∀ hb : some b ∉ excludedBranches d a S,
      ∀ α : S, IsConj (regularFibreAction hd ha S hb α).perm (γ α)) :
    TwistPointData d a S γ where
  points := points
  genus := genus
  degree := degree
  projection := projection
  branch := excludedBranches d a S
  infinity := mem_insert_self _ _
  branch_size := excludedBranches_card d a S
  hasse_weil := hasse_weil
  fibre_degree := fibre_degree
  specialization := fun p b hp hb α =>
    relabel_conjugate (regularFibreAction hd ha S hb α) (specialization p b hp hb α)

end
end BlockingCurves.CuspidalGeneral
