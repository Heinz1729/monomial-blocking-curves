import PhaseTraceLower
import PhaseCommonVariable
import NormFibreSampling

/-! Vertical translates of a Frobenius graph with arbitrary scalar labels.
The partition need not consist of cosets for the first-moment and trace results. -/
namespace BlockingCurves.PiecewiseFrobenius
open Finset NormPencil
open scoped BigOperators

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def branchMap (β : E → F) (x : E) : E :=
  algebraMap F E (β x) * x ^ Fintype.card F

/-- The character label after applying a branch determines injectivity of
the entire map whenever the induced map on labels is injective. -/
theorem permutation_of_label_map {J : Type*} (label : E → J) (c : J → Fˣ)
    (g : J → J) (hg : Function.Injective g)
    (h : ∀ x : E, x ≠ 0 →
      label (branchMap (fun y => (c (label y) : F)) x) = g (label x)) :
    Function.Bijective (branchMap (fun y => (c (label y) : F))) := by
  let f := branchMap (fun y => (c (label y) : F))
  have f0 : f 0 = 0 := by simp [f,branchMap,zero_pow Fintype.card_pos.ne']
  have nz (x : E) (hx : x ≠ 0) : f x ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap F E)).2 (c (label x)).ne_zero) (pow_ne_zero _ hx)
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have hi : Function.Injective f := by
    intro x y he
    by_cases hx : x = 0
    · subst x
      by_contra hn
      exact nz y (Ne.symm hn) (he.symm.trans f0)
    by_cases hy : y = 0
    · subst y
      exact (nz x hx (he.trans f0)).elim
    have same := hg ((h x hx).symm.trans ((congrArg label he).trans (h y hy)))
    change algebraMap F E (c (label x) : F)*x^Fintype.card F =
      algebraMap F E (c (label y) : F)*y^Fintype.card F at he
    rw [same] at he
    exact σ.injective (by rw [hσ,hσ]; exact mul_left_cancel₀ ((map_ne_zero (algebraMap F E)).2 (c (label y)).ne_zero) he)
  exact ⟨hi,Finite.surjective_of_injective hi⟩

/-- A common norm for all multipliers forces a hyperplane obstruction.
Only the number of distinct branch multipliers occurs in the denominator. -/
theorem common_norm_lower [FiniteDimensional F E] {n : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F ^ n) (β : E → F) (Z : Finset F)
    (labels : ∀ x, β x ∈ Z) (c : Fˣ) (norms : ∀ z ∈ Z, z^n = (c:F)^n)
    (S : Finset E) (blocks : GraphHits (branchMap β) (S : Set E)) :
    (Fintype.card F - 1)*n + 1 ≤ Z.card*S.card := by
  classical
  let μ : Set F := ↑Z
  letI : Nonempty μ := ⟨⟨β 0,labels 0⟩⟩
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let T : Module.End F E := (c:F) • σ.toLinearMap
  have eigen (z : μ) : ∃ w : E, T.HasEigenvector (z:F) w := by
    have hz : (z:F) ≠ 0 := by
      intro he
      have bad := norms z z.property
      rw [he,zero_pow hn.ne'] at bad
      exact pow_ne_zero n c.ne_zero bad.symm
    let u := Units.mk0 (z:F) hz / c
    have uv : (u:F)=(z:F)/(c:F) := by simp [u,Units.val_div_eq_div_val]
    have hu : u^n=1 := Units.ext (by
      rw [Units.val_pow_eq_pow_val,uv,div_pow,norms z z.property,div_self (pow_ne_zero _ c.ne_zero)]
      rfl)
    obtain ⟨w,hw,he⟩ := ExtensionPhase.exists_frobenius_eigenvector hn dvd_rfl size u hu
    refine ⟨w,Module.End.mem_eigenspace_iff.mpr ?_,hw⟩
    change (c:F) • σ w = (z:F) • w
    rw [hσ,he,Algebra.smul_def,Algebra.smul_def]
    rw [uv,← mul_assoc,← map_mul,mul_div_cancel₀ _ c.ne_zero]
  choose w hw using eigen
  have branches (x : E) : ∃ i : μ, T (w i*x) = w i*branchMap β x := by
    let i : μ := ⟨β x,labels x⟩
    refine ⟨i,?_⟩
    have hwi := Module.End.mem_eigenspace_iff.mp (hw i).1
    change (c:F) • σ (w i) = (β x) • w i at hwi
    change (c:F) • σ (w i*x) = _
    rw [map_mul,Algebra.smul_def,← mul_assoc]
    rw [Algebra.smul_def,Algebra.smul_def] at hwi
    rw [hwi,hσ]; unfold branchMap; ring
  have hlo := PhaseTraceLower.cardinal_lower w (Module.End.eigenvectors_linearIndependent T μ w hw)
    T (branchMap β) branches S blocks
  have dim : FiniteDimensional.finrank F E = n :=
    Nat.pow_right_injective Fintype.one_lt_card ((card_eq_pow_finrank (K:=F) (V:=E)).symm.trans size)
  have hcard : Fintype.card μ = Z.card := Fintype.card_coe _
  simpa only [dim,hcard] using hlo

/-- Two different norms guarantee an injective linearized branch for
every slope, even if some other branches are singular. -/
theorem separated_norm_branch {n : ℕ} (size : Fintype.card E = Fintype.card F ^ n)
    (z w : F) (sep : z^n ≠ w^n) (a : E) :
    ∃ u : F, (u=z ∨ u=w) ∧ Function.Injective
      (fun x : E => algebraMap F E u*x^Fintype.card F-a*x) := by
  let D := normExponent (Fintype.card F) n
  have diff : (algebraMap F E z)^D ≠ (algebraMap F E w)^D := by
    dsimp [D]; rw [← map_pow,← map_pow,scalar_norm_power,scalar_norm_power]
    exact fun h => sep ((algebraMap F E).injective h)
  by_cases h : a^D=(algebraMap F E z)^D
  · exact ⟨w,Or.inr rfl,ExtensionPhase.branch_injective_of_norm_ne size _ _ (h ▸ diff)⟩
  · exact ⟨z,Or.inl rfl,ExtensionPhase.branch_injective_of_norm_ne size _ _ h⟩

noncomputable def labelFibre (β : E → F) (z : F) : Finset E :=
  open Classical in univ.filter (fun x => x ≠ 0 ∧ β x=z)

noncomputable def hitRow (f : E → E) (a b : E) : Finset E :=
  open Classical in univ.image (fun x => f x-a*x-b)

/-- Each affine line can be hit by at least one entire branch's worth
of distinct parameters and also the parameter obtained at zero. -/
theorem separated_norm_hit_count {n e : ℕ} (size : Fintype.card E = Fintype.card F ^ n)
    (β : E → F) (z w : F) (sep : z^n ≠ w^n)
    (hz : e ≤ (labelFibre β z).card) (hw : e ≤ (labelFibre β w).card) (a b : E) :
    e+1 ≤ (hitRow (branchMap β) a b).card := by
  classical
  obtain ⟨u,hu,hi⟩ := separated_norm_branch size z w sep a
  let C := labelFibre β u
  let L (x : E) := algebraMap F E u*x^Fintype.card F-a*x
  let out (x : E) := L x-b
  have inj : Function.Injective out := fun _ _ h => hi (sub_left_inj.mp h)
  have hC (x : E) (hx : x ∈ C) : x ≠ 0 ∧ β x = u := (mem_filter.mp hx).2
  have zero : out 0 = -b := by simp [out,L,zero_pow Fintype.card_pos.ne']
  have absent : -b ∉ C.image out := by
    rintro mem
    obtain ⟨x,hx,h⟩ := mem_image.mp mem
    exact (hC x hx).1 (inj (h.trans zero.symm))
  have sub : insert (-b) (C.image out) ⊆ hitRow (branchMap β) a b := by
    intro y hy
    rcases mem_insert.mp hy with rfl|hy
    · exact mem_image.mpr ⟨0,mem_univ _,by simp [branchMap,zero_pow Fintype.card_pos.ne']⟩
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x,mem_univ _,by simp only [branchMap,(hC x hx).2,out,L]⟩
  have h := card_le_card sub
  rw [card_insert_of_not_mem absent,card_image_of_injective _ inj] at h
  rcases hu with rfl|rfl
  · exact (Nat.add_le_add_right hz 1).trans h
  · exact (Nat.add_le_add_right hw 1).trans h

/-- Independent samples meet every slope/intercept row if each contains
at least a fraction 1/m of the parameters. -/
theorem rows_upper_of_share {m : ℕ} (hm : 0 < m) (row : E×E → Finset E)
    (share : ∀ l, Fintype.card E ≤ m*(row l).card) :
    ∃ S : Finset E, (∀ l, ∃ a ∈ S, a ∈ row l) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  classical
  let q := Fintype.card E
  let k := ⌈2*(m:ℝ)*Real.log (2*q)⌉₊
  obtain ⟨lmin,_,minimal⟩ := exists_min_image (univ : Finset (E×E))
    (fun l => (row l).card) univ_nonempty
  let H := (row lmin).card
  let N := q-H
  have hit (l : E×E) : H ≤ (row l).card := minimal l (mem_univ _)
  have eq : N+H=q := Nat.sub_add_cancel (card_le_univ _)
  have qpos : (0:ℝ) < q := Nat.cast_pos.mpr Fintype.card_pos
  have mpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have ee : (N:ℝ)+(H:ℝ)=q := by exact_mod_cast eq
  have sh : (q:ℝ) ≤ m*(H:ℝ) := by exact_mod_cast share lmin
  have nohit : (N:ℝ) ≤ q*Real.exp (-(1/(m:ℝ))) := by
    have frac : (q:ℝ)/m ≤ (H:ℝ) := (div_le_iff mpos).2 (by linarith only [sh,mul_comm (m:ℝ) (H:ℝ) |>.le])
    calc (N:ℝ) ≤ q*(1-1/(m:ℝ)) := by rw [mul_sub,mul_one,mul_one_div]; linarith
         _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp (-(1/(m:ℝ)))]) qpos.le
  have qtwo : (2:ℝ) ≤ q := by exact_mod_cast (show 2 ≤ Fintype.card E from Fintype.one_lt_card)
  have logq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  have log2q : 0 ≤ Real.log (2*(q:ℝ)) := Real.log_nonneg (by linarith)
  have kceil : 2*(m:ℝ)*Real.log (2*q) ≤ k := Nat.le_ceil _
  have cut : PencilSampling.sampleCutoff q (1/2) (1/(m:ℝ)) (1/(m:ℝ)) 0 ≤ k := by
    apply le_trans _ kceil
    simp only [PencilSampling.sampleCutoff,Real.log_inv,Real.log_div one_ne_zero (by norm_num : (2:ℝ)≠0),
      Real.log_one,Real.log_mul (by norm_num : (2:ℝ)≠0) qpos.ne',zero_sub,sub_neg_eq_add,
      zero_div,add_zero,one_div,div_inv_eq_mul]
    apply max_le
    · nlinarith only [mul_nonneg logq mpos.le]
    · ring_nf; rfl
  have bound := PencilSampling.two_rate_size (q:=(q:ℝ)) (z:=(1/2:ℝ)) (H:=(N:ℝ)) (N:=(N:ℝ))
    (μ:=1/(m:ℝ)) (ν:=1/(m:ℝ)) (ε:=0) qtwo le_rfl
    (one_div_pos.mpr mpos) (one_div_pos.mpr mpos) le_rfl
    (by simpa using mul_nonneg (one_div_pos.mpr mpos).le (Real.sqrt_nonneg (q:ℝ)))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    nohit (by simpa using nohit) cut
  have budget : q^2*N^k < q^k := by
    have h₁ : 0 ≤ (q:ℝ)*(N:ℝ)^k := by positivity
    have h₂ : 0 < (q:ℝ)^k := pow_pos qpos _
    exact_mod_cast (show (q:ℝ)^2*(N:ℝ)^k < (q:ℝ)^k by linarith)
  have total : (∑ l : E×E, ∏ _i : Fin k, (Fintype.card E - (row l).card)) < Fintype.card E^Fintype.card (Fin k) := by
    calc _ ≤ ∑ _l : E×E, N^k := by
               apply sum_le_sum
               intro l _
               simp only [prod_const,card_univ,Fintype.card_fin]
               exact pow_le_pow_left' (Nat.sub_le_sub_left (hit l) _) _
         _ < _ := by simpa [q,pow_two,Fintype.card_prod] using budget
  obtain ⟨sample,all⟩ := NormFibreSampling.exists_transversal (fun l (_ : Fin k) => row l) total
  refine ⟨univ.image sample, ?_, ?_⟩
  · intro l
    obtain ⟨i,hi⟩ := all l
    exact ⟨sample i,mem_image.mpr ⟨i,mem_univ _,rfl⟩,hi⟩
  · have card : (univ.image sample).card ≤ k := card_image_le.trans_eq (by simp)
    exact (show ((univ.image sample).card:ℝ) ≤ k by exact_mod_cast card).trans
      (Nat.ceil_lt_add_one (mul_nonneg (by positivity) log2q)).le

/-- Independent point samples cover any graph when every line receives a
fraction at least 1/m of the parameters. -/
theorem graph_upper_of_share {m : ℕ} (hm : 0 < m) (f : E → E)
    (share : ∀ a b : E, Fintype.card E ≤ m*(hitRow f a b).card) :
    ∃ S : Finset E, GraphHits f (S : Set E) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  classical
  obtain ⟨S,hit,card⟩ := rows_upper_of_share hm (fun l : E×E => hitRow f l.1 l.2)
    (fun l => share l.1 l.2)
  refine ⟨S,?_,card⟩
  intro a b
  obtain ⟨y,hy,hrow⟩ := hit (a,b)
  obtain ⟨x,_,hx⟩ := mem_image.mp hrow
  exact ⟨x,hx ▸ hy⟩

/-- With an injective branch of density at least 1/m (including zero),
independent shifts give an actual cover of the translated graph. -/
theorem separated_norm_upper {n e m : ℕ} (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) (share : Fintype.card E ≤ m*(e+1))
    (β : E → F) (z w : F) (sep : z^n ≠ w^n)
    (hz : e ≤ (labelFibre β z).card) (hw : e ≤ (labelFibre β w).card) :
    ∃ S : Finset E, GraphHits (branchMap β) (S : Set E) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  apply graph_upper_of_share hm
  intro a b
  exact share.trans (Nat.mul_le_mul_left m (separated_norm_hit_count size β z w sep hz hw a b))

/-- Relabelling can merge whole cosets. Each coefficient assigned to a
realized label still occurs on at least (q−1)/m nonzero inputs. -/
theorem power_label_fibre {m : ℕ} (hm : m ∣ Fintype.card E-1) (table : E → F)
    (v : Eˣ) :
    let e := (Fintype.card E-1)/m
    e ≤ (labelFibre (fun x : E => table (x^e)) (table ((v:E)^e))).card := by
  classical
  intro e
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  let H := Subgroup.zpowers (g^m)
  have hc : Fintype.card H = e := by
    dsimp [H,e]
    rw [Fintype.card_zpowers,orderOf_pow g,orderOf_eq_card_of_forall_mem_zpowers hg,
      Fintype.card_units,Nat.gcd_eq_right hm]
  let f (u : H) : E := v * ((u.val:Eˣ):E)
  have inj : Function.Injective f := fun _ _ h => Subtype.ext (Units.ext (mul_left_cancel₀ v.ne_zero h))
  have sub : univ.image f ⊆ labelFibre (fun x:E => table (x^e)) (table ((v:E)^e)) := by
    intro x hx
    obtain ⟨u,_,rfl⟩ := mem_image.mp hx
    have h : u^e = 1 := hc ▸ pow_card_eq_one
    have heq := congrArg (fun y : H => ((y.val:Eˣ):E)) h
    change ((u.val:Eˣ):E)^e=1 at heq
    apply mem_filter.mpr
    exact ⟨mem_univ _,mul_ne_zero v.ne_zero u.val.ne_zero,by simp [f,mul_pow,heq]⟩
  simpa only [card_image_of_injective _ inj,card_univ,hc] using card_le_card sub

/-- Logarithmic upper bound on the actual cyclotomic table, with no
assumption on injectivity of the table or equal sizes of coefficient fibres. -/
theorem cyclotomic_table_upper {n m : ℕ} (hm : 0 < m) (divides : m ∣ Fintype.card E-1)
    (size : Fintype.card E = Fintype.card F^n) (table : E → F) (v w : Eˣ) :
    let e := (Fintype.card E-1)/m
    table ((v:E)^e)^n ≠ table ((w:E)^e)^n →
    ∃ S : Finset E, GraphHits (branchMap (fun x : E => table (x^e))) (S : Set E) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  intro e sep
  have product : e*m = Fintype.card E-1 := Nat.div_mul_cancel divides
  have qpos : 0 < Fintype.card E := Fintype.card_pos
  have share : Fintype.card E ≤ m*(e+1) := by rw [mul_add,mul_comm m e,product,mul_one]; omega
  exact separated_norm_upper hm size share _ _ _ sep
    (power_label_fibre divides table v) (power_label_fibre divides table w)

end BlockingCurves.PiecewiseFrobenius
