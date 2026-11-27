import PencilCollisionCover

/-! Index reduction and the relative error obtained with the horizontal lower
estimate of Zhou–Wu, Proposition 4.1. -/
namespace BlockingCurves.PencilCollisionCover
open Real
variable {F : Type*} [Field F] [Fintype F]

/-- The power-value set depends only on gcd(d,q-1), including zero. -/
theorem power_range_index (d : ℕ) (hd : 0 < d) :
    Set.range (fun x : F => x^d) = Set.range (fun x : F => x^(d.gcd (Fintype.card F-1))) := by
  let N := Fintype.card F-1
  let r := d.gcd N
  have hr : 0 < r := Nat.gcd_pos_of_pos_left _ hd
  ext a
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨k,hk⟩ := Nat.gcd_dvd_left d N
    exact ⟨x^k, by change (x^k)^r=x^d; rw [← pow_mul,Nat.mul_comm,← hk]⟩
  · rintro ⟨x,rfl⟩
    by_cases hx : x = 0
    · exact ⟨0,by simp [hx,zero_pow hr.ne',zero_pow hd.ne',r,N]⟩
    let g := Units.mk0 x hx
    have hN : g ^ N = 1 := Units.ext (FiniteField.pow_card_sub_one_eq_one x hx)
    have key := congrArg (fun n : ℤ => g^n) (Nat.gcd_eq_gcd_ab d N)
    dsimp only at key
    rw [zpow_add,zpow_mul',zpow_mul,zpow_natCast,zpow_natCast,zpow_natCast,hN,one_zpow,mul_one] at key
    exact ⟨((g^(Nat.gcdA d N) : Fˣ):F),congrArg Units.val key.symm⟩

theorem horizontal_minimum_index (F : Type*) [Field F] [Fintype F] (d : ℕ) (hd : 0 < d) :
    horizontalMinimum F d = horizontalMinimum F (d.gcd (Fintype.card F-1)) := by
  let r := d.gcd (Fintype.card F-1)
  have he := power_range_index (F := F) d hd
  have iffHits (T : Finset F) : horizontalHits d T ↔ horizontalHits r T := by
    constructor
    · intro hd b
      obtain ⟨x,hx⟩ := hd b
      obtain ⟨y,hy⟩ := he ▸ (Set.mem_range_self x : x^d ∈ Set.range (fun z : F => z^d))
      change y^r = x^d at hy
      exact ⟨y,by simpa only [hy] using hx⟩
    · intro hr b
      obtain ⟨x,hx⟩ := hr b
      obtain ⟨y,hy⟩ := he.symm ▸ (Set.mem_range_self x : x^r ∈ Set.range (fun z : F => z^r))
      change y^d = x^r at hy
      exact ⟨y,by simpa only [hy] using hx⟩
  obtain ⟨S,hS,hs⟩ := (horizontalMinimum_spec F d).1
  obtain ⟨T,hT,ht⟩ := (horizontalMinimum_spec F r).1
  exact le_antisymm ((horizontalMinimum_spec F d).2 ⟨T,hT,(iffHits T).2 ht⟩)
    ((horizontalMinimum_spec F r).2 ⟨S,hS,(iffHits S).1 hs⟩)

/-- Explicit upper estimate that does not divide by a logarithm depending on h. -/
theorem supplementSize_lt (q h : ℕ) (hq : 1 < q) (hh : 0 < h) :
    (supplementSize q h : ℝ) < 2*((h:ℝ)+1)*log q+1 := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast hq
  have hh0 : (0:ℝ) < h := by exact_mod_cast hh
  let a : ℝ := 1+1/(h:ℝ)
  have ha : 1 < a := by dsimp [a]; linarith only [one_div_pos.mpr hh0]
  have ha' : 0 < a := by linarith
  have hlog := log_pos ha
  have hb := log_le_sub_one_of_pos (inv_pos.mpr ha')
  rw [log_inv] at hb
  have hai : a⁻¹ = (h:ℝ)/(h+1) := by dsimp [a]; field_simp
  rw [hai] at hb
  have h₁ : (1:ℝ) ≤ (h+1)*log a := by
    have ht := mul_le_mul_of_nonneg_left hb (show 0 ≤ (h:ℝ)+1 by positivity)
    have he : ((h:ℝ)+1)*(h/(h+1)-1) = -1 := by field_simp
    linarith only [ht,he]
  have hL := log_nonneg hq1.le
  have h₂ : 2*log q/log a ≤ 2*((h:ℝ)+1)*log q := by
    apply (div_le_iff hlog).2
    nlinarith only [mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2*log q by positivity)]
  exact (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hL) hlog.le)).trans_le (by linarith only [h₂])

/-- Finite relative surplus after inserting the horizontal lower bound.
The sole external counting premise is Zhou–Wu Proposition 4.1 at the index r. -/
theorem relative_surplus_of_horizontal_lower (F : Type*) [Field F] [Fintype F]
    (d : ℕ) (hd : 2 ≤ d) (hr : 1 < d.gcd (Fintype.card F-1))
    (lower : let r := d.gcd (Fintype.card F-1)
      (r:ℝ)*log (Fintype.card F)/(8*log r) ≤ horizontalMinimum F r) :
    let q := Fintype.card F
    let r := d.gcd (q-1)
    let h := (d-1).gcd (q-1)
    ∃ B : ℕ, AsgarliGhiocaYip.isPencilMinimum F d B ∧
      1 ≤ (B:ℝ)/horizontalMinimum F d ∧
      (B:ℝ)/horizontalMinimum F d ≤
        1 + 8*(2*((h:ℝ)+1)+1/log q)*log r/r := by
  let q := Fintype.card F
  let r := d.gcd (q-1)
  let h := (d-1).gcd (q-1)
  let τ := horizontalMinimum F d
  have hq : 1 < q := Fintype.one_lt_card
  have hh : 0 < h := Nat.gcd_pos_of_pos_left _ (by omega)
  have hL : 0 < log q := log_pos (by exact_mod_cast hq)
  have hr' : (1:ℝ) < r := by exact_mod_cast hr
  have hρ : 0 < log r := log_pos hr'
  have hR : (0:ℝ) < r := zero_lt_one.trans hr'
  have hlo : (r:ℝ)*log q/(8*log r) ≤ τ := by
    dsimp only [τ]
    rw [horizontal_minimum_index F d (by omega)]
    exact lower
  have hτ : 0 < (τ:ℝ) := (div_pos (mul_pos hR hL) (by positivity)).trans_le hlo
  obtain ⟨B,hB,hle,hgap⟩ := variable_degree_minimum_gap F d hd
  have hb : τ ≤ B := hle
  have hsub : (B:ℝ)-(τ:ℝ) ≤ (supplementSize q h : ℝ) := by
    rw [← Nat.cast_sub hb]
    exact_mod_cast hgap
  let M : ℝ := 2*((h:ℝ)+1)*log q+1
  have he : 8*(2*((h:ℝ)+1)+1/log q)*log r/r =
      M / ((r:ℝ)*log q/(8*log r)) := by
    dsimp [M]; field_simp; ring
  refine ⟨B,hB,(one_le_div hτ).2 (by exact_mod_cast hb),?_⟩
  change (B:ℝ)/(τ:ℝ) ≤ 1 + 8*(2*((h:ℝ)+1)+1/log q)*log r/r
  rw [he]
  have ha : (B:ℝ)-(τ:ℝ) ≤ M := hsub.trans (supplementSize_lt q h hq hh).le
  have hdiv := div_le_div_of_nonneg_left (show 0 ≤ M by dsimp [M]; positivity)
    (show 0 < (r:ℝ)*log q/(8*log r) by positivity) hlo
  have H := (div_le_div_right hτ).mpr ha
  rw [sub_div,div_self hτ.ne'] at H
  linarith only [H,hdiv]


/-- Along an arbitrary family of finite fields, the explicit relative error
goes to zero under (h+1)log r / r → 0. The only outside estimate is the
Zhou--Wu horizontal lower bound at the actual index r. -/
theorem variable_ratio_tendsto {I : Type*} (l : Filter I)
    (F : I → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    (d B : I → ℕ) (hd : ∀ i, 2 ≤ d i)
    (hB : ∀ i, AsgarliGhiocaYip.isPencilMinimum (F i) (d i) (B i))
    (hr : ∀ i, 1 < (d i).gcd (Fintype.card (F i)-1))
    (lower : ∀ i, let r := (d i).gcd (Fintype.card (F i)-1)
      (r:ℝ)*log (Fintype.card (F i))/(8*log r) ≤ horizontalMinimum (F i) r)
    (vanish : Filter.Tendsto (fun i =>
      let q := Fintype.card (F i)
      let r := (d i).gcd (q-1)
      let h := (d i-1).gcd (q-1)
      ((h:ℝ)+1)*log r/r) l (nhds 0)) :
    Filter.Tendsto (fun i => (B i:ℝ)/horizontalMinimum (F i) (d i)) l (nhds 1) := by
  let err (i : I) :=
    let q := Fintype.card (F i)
    let r := (d i).gcd (q-1)
    let h := (d i-1).gcd (q-1)
    ((h:ℝ)+1)*log r/r
  have bounds (i : I) : 1 ≤ (B i:ℝ)/horizontalMinimum (F i) (d i) ∧
      (B i:ℝ)/horizontalMinimum (F i) (d i) ≤ 1+32*err i := by
    obtain ⟨b, hb, hlo, hhi⟩ := relative_surplus_of_horizontal_lower (F i) (d i) (hd i) (hr i) (lower i)
    have eq' : b = B i := ((AGY_minimum_iff (hd i) _).1 hb).unique
      ((AGY_minimum_iff (hd i) _).1 (hB i))
    subst b
    refine ⟨hlo,hhi.trans ?_⟩
    let r := (d i).gcd (Fintype.card (F i)-1)
    let h := (d i-1).gcd (Fintype.card (F i)-1)
    let L := log (Fintype.card (F i))
    have hq : (2:ℝ) ≤ Fintype.card (F i) := by exact_mod_cast Fintype.one_lt_card (α := F i)
    have aux := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [log_inv] at aux
    norm_num at aux
    have hL : (1/2:ℝ) ≤ L := by
      dsimp [L]
      linarith only [aux,log_le_log (by norm_num : (0:ℝ)<2) hq]
    have hL' : 1/L ≤ 2 := (div_le_iff (by linarith : 0<L)).2 (by linarith)
    have hr' : (1:ℝ) < r := by exact_mod_cast hr i
    have hm : 8*(2*((h:ℝ)+1)+1/L) ≤ 32*((h:ℝ)+1) := by linarith [Nat.cast_nonneg (α := ℝ) h]
    change 1+8*(2*((h:ℝ)+1)+1/L)*log r/r ≤ 1+32*(((h:ℝ)+1)*log r/r)
    rw [← mul_div_assoc, ← mul_assoc 32]
    gcongr
  have htop : Filter.Tendsto (fun i => 1+32*err i) l (nhds 1) := by
    simpa using (tendsto_const_nhds.add (tendsto_const_nhds.mul vanish) :
      Filter.Tendsto (fun i => 1+32*err i) l (nhds ((1:ℝ)+32*0)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htop
    (Filter.eventually_of_forall fun i => (bounds i).1)
    (Filter.eventually_of_forall fun i => (bounds i).2)
end BlockingCurves.PencilCollisionCover
