import PhaseDividingMinimum
import PiecewiseFrobenius
import PiecewiseCandidates

/-! A single cyclotomic class supplies a uniform cover. The other classes
may carry arbitrary values, including repeated coefficients. -/
namespace BlockingCurves.PiecewiseFrobenius

open Finset PhaseDirection PhaseDividing Polynomial
open scoped Polynomial
attribute [local instance] Classical.propDecidable

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private theorem restricted_fibre (D : Finset E) (a b y : E) :
    (D.filter (fun x : E => x^Fintype.card F-a*x-b=y)).card ≤ Fintype.card F := by
  classical
  let s := Fintype.card F
  let Q : E[X] := C a*X + C (b+y)
  let P : E[X] := X^s-Q
  have hs : 1 < s := Fintype.one_lt_card
  have hQ : Q.natDegree ≤ 1 := by dsimp [Q]; compute_degree
  have deg : P.natDegree=s := by
    dsimp only [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt, natDegree_X_pow]
    simpa only [natDegree_X_pow] using hQ.trans_lt hs
  have nz : P ≠ 0 := by intro h; simp [h] at deg; omega
  apply le_trans _ deg.le
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  have h := (Finset.mem_filter.mp hx).2
  apply (Polynomial.mem_roots nz).2
  simp only [P,Q,Polynomial.IsRoot,eval_sub,eval_pow,eval_X,eval_add,eval_mul,eval_C]
  change x^s-a*x-b=y at h
  linear_combination h

/-- The point sampler only uses zero and the class of character value one.
Every fibre on this domain has size at most the ground-field order. -/
private theorem restricted_share (H : Subgroup Eˣ) {m : ℕ} (hm : 0 < m)
    (order : m*(carrier H).card+1=Fintype.card E) (f : E → E) (zero : f 0=0)
    (branch : ∀ x ∈ carrier H, f x=x^Fintype.card F) (a b : E) :
    Fintype.card E ≤ (m*Fintype.card F)*(hitRow f a b).card := by
  classical
  let D := insert (0:E) (carrier H)
  let L := fun x : E => x^Fintype.card F-a*x-b
  have outside : (0:E) ∉ carrier H := by
    rintro h
    obtain ⟨u,_,h⟩ := mem_image.mp h
    exact u.val.ne_zero h
  have hd : D.card = (carrier H).card+1 := card_insert_of_not_mem outside
  have inside : D.image L ⊆ hitRow f a b := by
    rintro _ hy
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    refine mem_image.mpr ⟨x,mem_univ _,?_⟩
    rcases mem_insert.mp hx with rfl|hx
    · simp [L,zero,zero_pow Fintype.card_pos.ne']
    · simp [L,branch x hx]
  have bound : D.card ≤ Fintype.card F*(D.image L).card :=
    card_le_mul_card_image D _ (fun y _ => restricted_fibre (F := F) D a b y)
  calc
    Fintype.card E ≤ m*D.card := by rw [←order,hd,Nat.mul_add,Nat.mul_one]; omega
    _ ≤ m*(Fintype.card F*(hitRow f a b).card) :=
      Nat.mul_le_mul_left _ (bound.trans (Nat.mul_le_mul_left _ (card_le_card inside)))
    _ = _ := (Nat.mul_assoc _ _ _).symm

/-- If a graph agrees with Frobenius on the subgroup, the singular-direction
variance controls the actual bad blocks, even at the singular slopes. -/
private theorem restricted_block {m : ℕ} (hm : 0 < m) (H : Subgroup Eˣ)
    (index : H.index=m) (order : m*(carrier H).card+1=Fintype.card E)
    (f : E → E) (branch : ∀ x ∈ carrier H, f x=x^Fintype.card F) (a b : E) :
    (emptyCount (fun p:E×E => hits F (hitRow f a b) p.1 p.2):ℝ) /
      (Fintype.card E:ℝ)^2 ≤ (1+2*(m:ℝ)^2)/Fintype.card F := by
  classical
  let G := (carrier H).image (fun x:E => x^Fintype.card F-a*x)
  have inside (y:E) (hy:y ∈ G) : y-b ∈ hitRow f a b := by
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
    exact mem_image.mpr ⟨x,mem_univ _,by rw [branch x hx]⟩
  have miss := empty_le_of_translate (F := F) G (hitRow f a b) b inside
  apply le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr miss) (sq_nonneg _))
  apply le_trans (frobenius_block_bound (F := F) H a)
  rw [index]
  exact rate Fintype.card_pos Fintype.one_lt_card hm order

/-- A bound for the whole graph obtained from its restriction to one
nonzero Frobenius class. No norm condition is needed for this direction. -/
theorem one_class_uniform_upper {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (size : Fintype.card E=Fintype.card F^n) (H : Subgroup Eˣ) (index : H.index=m)
    (order : m*(carrier H).card+1=Fintype.card E) (f : E → E) (zero : f 0=0)
    (branch : ∀ x ∈ carrier H, f x=x^Fintype.card F) :
    ∃ S : Finset E, GraphHits f (S:Set E) ∧
      S.card ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  by_cases small : Fintype.card F < (1+2*m^2)^2
  · obtain ⟨S,hS,h⟩ := graph_upper_of_share (Nat.mul_pos (by omega : 0<m) Fintype.card_pos)
      f (restricted_share H (by omega) order f zero branch)
    refine ⟨S,hS,?_⟩
    have hs : (1:ℝ) ≤ Fintype.card F := by exact_mod_cast (Nat.le_of_lt (Fintype.one_lt_card (α := F)))
    have nn : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hg : (Fintype.card F:ℝ) ≤ (1+2*(m:ℝ)^2)^2 := by exact_mod_cast small.le
    have hlog : Real.log (2*(Fintype.card E:ℝ)) ≤ n*(1+(1+2*(m:ℝ)^2)^2) := by
      rw [size,Nat.cast_pow,Real.log_mul (by norm_num) (pow_pos (by linarith) n).ne',Real.log_pow]
      have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      have base := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ)<Fintype.card F)
      nlinarith only [h2,nn,mul_le_mul_of_nonneg_left (base.trans
        (by linarith : (Fintype.card F:ℝ)-1 ≤ (1+2*(m:ℝ)^2)^2)) (by positivity : (0:ℝ) ≤ n)]
    have hs1 : (1:ℝ) ≤ n*(Fintype.card F:ℝ) := nn.trans
      (by simpa using mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ n))
    simp only [Nat.cast_mul] at h
    have finalR : (S.card:ℝ) ≤ (2*(m:ℝ)*(1+(1+2*(m:ℝ)^2)^2)+1)*n*Fintype.card F := by
      nlinarith only [h,hs1,mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 2*m*Fintype.card F)]
    exact_mod_cast finalR
  · obtain ⟨S,hS,h⟩ := graph_block_sampling f size (A := 1+2*(m:ℝ)^2)
      (by nlinarith only [sq_nonneg (m:ℝ)]) (by exact_mod_cast Nat.le_of_not_lt small)
      (restricted_block (by omega) H index order f branch)
    refine ⟨S,hS,h.trans (Nat.mul_le_mul_right _ ?_)⟩
    have four : 4 ≤ 2*m*(1+(1+2*m^2)^2) := by
      calc 4 ≤ 2*m := by omega
           _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
    have haux := Nat.mul_le_mul_right n four
    rw [Nat.add_mul,one_mul]
    omega

/-- The label-one coefficient can be normalized by scaling the ordinate.
Only this coefficient has to be nonzero. -/
theorem cyclotomic_table_uniform_upper {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (divides : m ∣ Fintype.card F-1) (size : Fintype.card E=Fintype.card F^n)
    (table : E → F) (unit : table 1 ≠ 0) :
    let e := (Fintype.card E-1)/m
    ∃ S : Finset E, GraphHits (branchMap (fun x:E => table (x^e))) (S:Set E) ∧
      S.card ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  classical
  intro e
  let c := algebraMap F E (table 1)
  have hc : c ≠ 0 := (_root_.map_ne_zero (algebraMap F E)).2 unit
  let f := branchMap (fun x:E => table (x^e))
  let g := fun x:E => f x/c
  obtain ⟨H,index,order,character⟩ := actual_branch_group divides size
  have same (x:E) (hx:x ∈ carrier H) : g x=x^Fintype.card F := by
    change algebraMap F E (table (x^e))*x^Fintype.card F/c=_
    rw [character x hx]
    exact mul_div_cancel_left₀ _ hc
  obtain ⟨T,hT,hcard⟩ := one_class_uniform_upper hm hn size H index order g
    (by simp [g,f,branchMap,zero_pow Fintype.card_pos.ne']) same
  refine ⟨T.image (fun z => c*z),?_,card_image_le.trans hcard⟩
  intro a b
  obtain ⟨x,hx⟩ := hT (a/c) (b/c)
  refine ⟨x,mem_image.mpr ⟨_,hx,?_⟩⟩
  change c*(f x/c-a/c*x-b/c)=f x-a*x-b
  field_simp [hc]

/- The coefficient set is taken after merging labels, so the lower bound
keeps the number of distinct coefficients rather than the cyclotomic index. -/
noncomputable def tableCoefficients (m : ℕ) (table : E → Fˣ) : Finset Fˣ :=
  open Classical in (Polynomial.nthRootsFinset m E).image table

theorem tableCoefficients_card_le (m : ℕ) (table : E → Fˣ) :
    (tableCoefficients m table).card ≤ m := by
  classical
  apply (Finset.card_image_le (s := Polynomial.nthRootsFinset m E) (f := table)).trans
  rw [Polynomial.nthRootsFinset_def]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

/-- When the coefficient period divides the extension degree, the minimum
itself satisfies both bounds. The table value assigned to label zero is
immaterial; zero belongs to the graph for every assignment. -/
theorem synchronous_table_minimum [FiniteDimensional F E] {m n : ℕ}
    (hm : 2 ≤ m) (hn : 0 < n) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E=Fintype.card F^n) (table : E → Fˣ)
    (phase : PiecewiseCandidates.coefficientPeriod (tableCoefficients m table) (table 1) ∣ n) :
    let e := (Fintype.card E-1)/m
    let f := branchMap (fun x:E => (table (x^e):F))
    ∃ S : Finset E, GraphHits f (S:Set E) ∧
      (∀ T : Finset E, GraphHits f (T:Set E) → S.card ≤ T.card) ∧
      (Fintype.card F-1)*n+1 ≤ (tableCoefficients m table).card*S.card ∧
      S.card ≤ (2*m*(1+(1+2*m^2)^2)+1)*n*Fintype.card F := by
  classical
  intro e f
  let C := tableCoefficients m table
  let Z := C.image (fun u : Fˣ => (u:F))
  let β (x:E) := if x=0 then (table 1:F) else (table (x^e):F)
  have dq : m ∣ Fintype.card E-1 := by
    rw [size,← NormPencil.normExponent_mul (Fintype.card F) n Fintype.card_pos,Nat.add_sub_cancel]
    exact dvd_mul_of_dvd_right divides _
  have member (z:E) (hz:z^m=1) : table z ∈ C :=
    mem_image.mpr ⟨z,(Polynomial.mem_nthRootsFinset (by omega)).2 hz,rfl⟩
  have labels (x:E) : β x ∈ Z := by
    by_cases hx : x=0
    · exact mem_image.mpr ⟨table 1,member 1 (one_pow _),by simp [β,hx]⟩
    · have hpow : (x^e)^m=1 := by
        rw [←pow_mul, show e*m = Fintype.card E-1 from Nat.div_mul_cancel dq]
        exact FiniteField.pow_card_sub_one_eq_one _ hx
      exact mem_image.mpr ⟨_,member _ hpow,by simp [β,hx]⟩
  have norms (z:F) (hz:z ∈ Z) : z^n=(table 1:F)^n := by
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    exact congrArg Units.val ((PiecewiseCandidates.coefficientPeriod_dvd_iff _ _ _).1 phase c hc)
  have maps : branchMap β=f := by
    funext x
    by_cases hx : x=0
    · simp [f,branchMap,hx,zero_pow Fintype.card_pos.ne']
    · simp only [f,branchMap,β,if_neg hx]
  obtain ⟨T,hT,bound⟩ := cyclotomic_table_uniform_upper hm hn divides size
    (fun x:E => (table x:F)) (table 1).ne_zero
  let feasible := (univ : Finset (Finset E)).filter (fun V : Finset E => GraphHits f (V:Set E))
  have hfeas (V : Finset E) : V ∈ feasible ↔ GraphHits f (V:Set E) := by simp [feasible]
  obtain ⟨S,hS,least⟩ := exists_min_image feasible Finset.card ⟨T,(hfeas _).2 hT⟩
  have hs := (hfeas _).1 hS
  refine ⟨S,hs,fun V hv => least _ ((hfeas _).2 hv),?_,
    (least _ ((hfeas _).2 hT)).trans bound⟩
  have lower := common_norm_lower hn size β Z labels (table 1) norms S (by rwa [maps])
  have eq : Z.card=C.card := card_image_of_injective _ (fun _ _ h => Units.ext h)
  simpa only [eq] using lower

end BlockingCurves.PiecewiseFrobenius
