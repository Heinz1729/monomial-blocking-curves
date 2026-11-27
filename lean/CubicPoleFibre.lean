import CubicRepairPlaces

/-! Residues of simultaneous regular functions at rational places. A bounded
rational function distinguishing regular elements from poles supplies finite
interpolation, without a weak approximation theorem. -/
namespace BlockingCurves.CubicPoleFibre
open CubicAlteration CubicRepairPlaces
open BigOperators
universe u v
variable {F : Type u} {K : Type v} [Field F] [Field K] [Algebra (RatFunc F) K]
variable {p : RationalPlace F K} {x y : K} {a b : F}

/-- The function is regular at the given place, with the specified residue. -/
def Value (p : RationalPlace F K) (x : K) (a : F) : Prop :=
  ∃ h : x ∈ p.ring, p.residue ⟨x,h⟩ = a

private theorem value_iff :
    Value p x a ↔ ∃ z : p.ring, p.ring.subtype z = x ∧ p.residue z = a := by
  constructor
  · rintro ⟨h,ha⟩; exact ⟨⟨x,h⟩,rfl,ha⟩
  · rintro ⟨z,rfl,rfl⟩; exact ⟨z.property,rfl⟩

theorem Value.unique (h : Value p x a) (h' : Value p x b) : a = b :=
  h.choose_spec.symm.trans h'.choose_spec

theorem value_zero (p : RationalPlace F K) : Value p 0 0 := value_iff.mpr ⟨0,map_zero _,map_zero _⟩
theorem value_one (p : RationalPlace F K) : Value p 1 1 := value_iff.mpr ⟨1,map_one _,map_one _⟩
theorem value_const (p : RationalPlace F K) (a : F) : Value p (baseConstant F K a) a :=
  ⟨p.constants a,p.on_constants a⟩

theorem Value.add (hx : Value p x a) (hy : Value p y b) : Value p (x+y) (a+b) := by
  obtain ⟨u,rfl,rfl⟩ := value_iff.mp hx
  obtain ⟨v,rfl,rfl⟩ := value_iff.mp hy
  exact value_iff.mpr ⟨u+v,map_add _ _ _,map_add _ _ _⟩

theorem Value.sub (hx : Value p x a) (hy : Value p y b) : Value p (x-y) (a-b) := by
  obtain ⟨u,rfl,rfl⟩ := value_iff.mp hx
  obtain ⟨v,rfl,rfl⟩ := value_iff.mp hy
  exact value_iff.mpr ⟨u-v,map_sub _ _ _,map_sub _ _ _⟩

theorem Value.mul (hx : Value p x a) (hy : Value p y b) : Value p (x*y) (a*b) := by
  obtain ⟨u,rfl,rfl⟩ := value_iff.mp hx
  obtain ⟨v,rfl,rfl⟩ := value_iff.mp hy
  exact value_iff.mpr ⟨u*v,map_mul _ _ _,map_mul _ _ _⟩

theorem Value.pow (hx : Value p x a) (n : ℕ) : Value p (x^n) (a^n) := by
  obtain ⟨u,rfl,rfl⟩ := value_iff.mp hx
  exact value_iff.mpr ⟨u^n,map_pow _ _ _,map_pow _ _ _⟩

theorem Value.inv (hx : Value p x a) (ha : a ≠ 0) : Value p x⁻¹ a⁻¹ := by
  obtain ⟨z,rfl,rfl⟩ := value_iff.mp hx
  have hker := LocalRing.ker_eq_maximalIdeal p.residue (fun c => ⟨_,p.on_constants c⟩)
  have hu : IsUnit z := by
    by_contra hn
    have hm : z ∈ LocalRing.maximalIdeal p.ring := hn
    exact ha ((RingHom.mem_ker p.residue).mp (hker.symm ▸ hm))
  obtain ⟨u,rfl⟩ := hu
  apply value_iff.mpr
  refine ⟨↑u⁻¹,?_,?_⟩ <;> simp

theorem value_inv_of_pole (p : RationalPlace F K) {x : K} (h : x ∉ p.ring) : Value p x⁻¹ 0 := by
  have hin := (p.ring.mem_or_inv_mem x).resolve_left h
  let c := p.residue ⟨x⁻¹,hin⟩
  have hc : Value p x⁻¹ c := ⟨hin,rfl⟩
  by_cases hz : c = 0
  · exact hz ▸ hc
  · have hv := hc.inv hz
    rw [inv_inv] at hv
    exact (h hv.choose).elim


theorem value_prod {I : Type*} (S : Finset I) (f : I → K) (c : I → F)
    (h : ∀ i ∈ S, Value p (f i) (c i)) :
    Value p (∏ i ∈ S, f i) (∏ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using value_one p
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem value_sum {I : Type*} (S : Finset I) (f : I → K) (c : I → F)
    (h : ∀ i ∈ S, Value p (f i) (c i)) :
    Value p (∑ i ∈ S, f i) (∑ i ∈ S, c i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using value_zero p
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The residue map fixing F is determined by the valuation ring: it is
surjective and its kernel is the unique maximal ideal. -/
theorem place_ext {p₁ p₂ : RationalPlace F K} (e : p₁.ring = p₂.ring) : p₁ = p₂ := by
  cases p₁ with
  | mk O hO v hv =>
    cases p₂ with
    | mk O' hO' w hw =>
      change O = O' at e
      subst O'
      have hk : RingHom.ker v = RingHom.ker w :=
        (LocalRing.ker_eq_maximalIdeal v (fun c => ⟨_,hv c⟩)).trans
          (LocalRing.ker_eq_maximalIdeal w (fun c => ⟨_,hw c⟩)).symm
      have he : v = w := by
        ext z
        let c : O := ⟨baseConstant F K (v z), hO _⟩
        have hz : z-c ∈ RingHom.ker v := by
          rw [RingHom.mem_ker, map_sub, show v c = v z from hv _ , sub_self]
        rw [hk, RingHom.mem_ker, map_sub, show w c = v z from hw _, sub_eq_zero] at hz
        exact hz.symm
      subst w
      rfl

variable [Fintype F]

/-- This rational function has residue one on regular inputs and zero at a pole. -/
private noncomputable def cutoff (F : Type u) [Field F] [Fintype F] (x : K) : K :=
  (1+x^(Fintype.card F)-x)⁻¹

private theorem cutoff_regular (p : RationalPlace F K) (x : K) (hx : x ∈ p.ring) :
    Value p (cutoff F x) 1 := by
  let a := p.residue ⟨x,hx⟩
  have h : Value p x a := ⟨hx,rfl⟩
  have he := ((value_one p).add (h.pow (Fintype.card F))).sub h
  rw [FiniteField.pow_card, add_sub_cancel_right] at he
  simpa [cutoff] using he.inv one_ne_zero

private theorem cutoff_pole (p : RationalPlace F K) (x : K) (hx : x ∉ p.ring) :
    Value p (cutoff F x) 0 := by
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := F)).ne'
  have hnpos : n ≠ 0 := by have hc := Fintype.one_lt_card (α := F); omega
  have hx0 : x ≠ 0 := fun hz => hx (hz ▸ p.ring.zero_mem)
  have hy := value_inv_of_pole p hx
  have d := ((hy.pow (n+1)).add (value_one p)).sub (hy.pow n)
  simp only [zero_pow (Nat.succ_ne_zero _), zero_pow hnpos, zero_add, sub_zero] at d
  have u := (hy.pow (n+1)).mul (d.inv one_ne_zero)
  simp only [zero_pow (Nat.succ_ne_zero _),zero_mul] at u
  unfold cutoff
  rw [hn]
  have c : (1+x^(n+1)-x)*(x⁻¹)^(n+1) = (x⁻¹)^(n+1)+1-(x⁻¹)^n := by
    rw [sub_mul,add_mul,one_mul, ← mul_pow,mul_inv_cancel hx0,one_pow]
    congr 1
    rw [pow_succ',←mul_assoc,mul_inv_cancel hx0,one_mul]
  have eq : (1+x^(n+1)-x)⁻¹ = (x⁻¹)^(n+1)*((x⁻¹)^(n+1)+1-(x⁻¹)^n)⁻¹ := by
    rw [← c, mul_inv_rev, ← mul_assoc, mul_inv_cancel (pow_ne_zero _ (inv_ne_zero hx0)), one_mul]
  exact eq.symm ▸ u

private theorem cutoff_values (p : RationalPlace F K) (x : K) :
    ∃ a : F, Value p (cutoff F x) a := by
  by_cases h : x ∈ p.ring
  · exact ⟨1,cutoff_regular p x h⟩
  · exact ⟨0,cutoff_pole p x h⟩

private theorem separate (p q : RationalPlace F K) (h : p ≠ q) :
    ∃ x : K, Value p x 1 ∧ Value q x 0 ∧ ∀ r : RationalPlace F K, ∃ a : F, Value r x a := by
  by_cases hpq : p.ring ≤ q.ring
  · have hqp : ¬ q.ring ≤ p.ring := fun h' => h (place_ext (le_antisymm hpq h'))
    obtain ⟨y,hyq,hyp⟩ := SetLike.not_le_iff_exists.mp hqp
    refine ⟨1-cutoff F y,?_,?_,?_⟩
    · simpa only [sub_zero] using (value_one p).sub (cutoff_pole p y hyp)
    · simpa only [sub_self] using (value_one q).sub (cutoff_regular q y hyq)
    · intro r
      obtain ⟨c,hc⟩ := cutoff_values r y
      exact ⟨1-c,(value_one r).sub hc⟩
  · obtain ⟨y,hyp,hyq⟩ := SetLike.not_le_iff_exists.mp hpq
    exact ⟨cutoff F y,cutoff_regular p y hyp,cutoff_pole q y hyq,fun r => cutoff_values r y⟩

/-- Simultaneous rational residue interpolation, with no restriction on the
number of prescribed places. Each basis function takes value one at its own
place and zero at every other listed place. -/
theorem selectors_field (P : Finset (RationalPlace F K)) : ∃ s : P → K, ∀ i j : P, by
    classical exact Value j.val (s i) (if i = j then 1 else 0) := by
  classical
  have pair (i j : P) : ∃ x : K, Value i.val x 1 ∧ (i ≠ j → Value j.val x 0) ∧
      ∀ r : P, ∃ a : F, Value r.val x a := by
    by_cases he : i = j
    · exact ⟨1,value_one _,by simp [he],fun r => ⟨1,value_one _⟩⟩
    · obtain ⟨x,hi,hj,hr⟩ := separate i.val j.val (fun e => he (Subtype.ext e))
      exact ⟨x,hi,fun _ => hj,fun r => hr r.val⟩
  choose f one zero regular using pair
  choose c val using regular
  refine ⟨fun i => ∏ j, f i j,?_⟩
  intro i j
  have hv := value_prod Finset.univ (f i) (fun k => c i k j) (fun k _ => val i k j)
  by_cases hij : i = j
  · subst j
    have ones (k : P) : c i k i = 1 := (val i k i).unique (one i k)
    simpa [ones] using hv
  · rw [if_neg hij]
    have hz : ∏ k, c i k j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) ((val i j j).unique (zero i j hij))
    rwa [hz] at hv

/-- Rational-place interpolation for a cubic branch. -/
theorem selectors {R : Finset (Line F)} {D : Branch F R} (P : Finset (Place D)) :
    ∃ s : P → D.K, ∀ i j : P, by classical exact Value j.val (s i) (if i = j then 1 else 0) :=
  selectors_field P

end BlockingCurves.CubicPoleFibre
