import NormPencilField
import PencilAsymptotic

/-! The nonsingular cyclotomic branch when the index does not divide the
relative degree, and the resulting unconditional projective sampling bound. -/
namespace BlockingCurves.ExtensionPhase

open Finset NormPencil

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

private theorem normExponent_modEq (s n m : ℕ) (hs : 1 ≤ s) (hm : m ∣ s-1) :
    Nat.ModEq m (normExponent s n) n := by
  have h : Nat.ModEq m s 1 := ((Nat.modEq_iff_dvd' hs).2 hm).symm
  induction n with
  | zero => rfl
  | succ n ih => simpa [normExponent] using ih.add (h.pow n)

private theorem normExponent_size {n : ℕ} (size : Fintype.card E = Fintype.card F ^ n) :
    (Fintype.card F-1)*normExponent (Fintype.card F) n = Fintype.card E-1 := by
  rw [size, ← normExponent_mul (Fintype.card F) n (Nat.le_of_lt Fintype.one_lt_card),
    Nat.add_sub_cancel, mul_comm]

/-- A collision in the linearized branch forces the indicated norm equality,
including horizontal slopes and characteristic dividing the extension degree. -/
theorem branch_injective_of_norm_ne {n : ℕ}
    (size : Fintype.card E = Fintype.card F ^ n) (z a : E)
    (h : a ^ normExponent (Fintype.card F) n ≠ z ^ normExponent (Fintype.card F) n) :
    Function.Injective (fun x : E => z*x^Fintype.card F-a*x) := by
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  intro x y hxy
  by_contra ne
  have hsub : (x-y)^Fintype.card F = x^Fintype.card F-y^Fintype.card F := by
    rw [← hσ, map_sub, hσ, hσ]
  have hz : z*(x-y)^(Fintype.card F-1) = a := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr ne) (b := x-y)
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.le_of_lt (Fintype.one_lt_card (α := F))), hsub]
    dsimp at hxy
    linear_combination hxy
  apply h
  rw [← hz,mul_pow,← pow_mul,normExponent_size size,
    FiniteField.pow_card_sub_one_eq_one _ (sub_ne_zero.mpr ne), mul_one]

/-- The criterion is sharp for every nonzero slope and branch multiplier:
equal norms give a nonzero kernel vector. -/
theorem branch_injective_iff_norm_ne {n : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F^n) (z a : Eˣ) :
    Function.Injective (fun x:E => (z:E)*x^Fintype.card F-(a:E)*x) ↔
      (a:E)^normExponent (Fintype.card F) n ≠ (z:E)^normExponent (Fintype.card F) n := by
  classical
  refine ⟨?_,branch_injective_of_norm_ne size z a⟩
  intro inj same
  let s := Fintype.card F
  let D := normExponent s n
  have hD : 0 < D := normExponent_pos Fintype.card_pos hn
  have hratio : (a/z)^D = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val,Units.val_div_eq_div_val,Units.val_one]
    rw [div_pow,same,div_self (pow_ne_zero _ z.ne_zero)]
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  obtain ⟨j,hj⟩ := mem_powers_iff_mem_zpowers.2 (hg (a/z))
  change g^j = a/z at hj
  have hjD : orderOf g ∣ j*D := orderOf_dvd_of_pow_eq_one (by rw [pow_mul,hj,hratio])
  rw [orderOf_eq_card_of_forall_mem_zpowers hg,Fintype.card_units,← normExponent_size size] at hjD
  obtain ⟨k,hk⟩ := Nat.dvd_of_mul_dvd_mul_right hD hjD
  let w := g^k
  have hw : w^(s-1) = a/z := by rw [← hj,hk,mul_comm,pow_mul]
  have hv : (w:E)^(s-1) = (a:E)/(z:E) := by
    simpa only [Units.val_pow_eq_pow_val,Units.val_div_eq_div_val] using congrArg (fun u:Eˣ => (u:E)) hw
  have he : (z:E)*(w:E)^(s-1) = (a:E) := by rw [hv,mul_div_cancel₀ _ z.ne_zero]
  have hz : (z:E)*(w:E)^s-(a:E)*(w:E) = 0 := by
    rw [show s = (s-1)+1 from (Nat.sub_add_cancel (Nat.le_of_lt (Fintype.one_lt_card (α := F)))).symm,
      pow_succ,← mul_assoc,he,sub_self]
  apply w.ne_zero
  apply inj
  simpa [zero_pow Fintype.card_pos.ne'] using hz

/-- For every slope at least one actual coset has an invertible linearized branch.
The other branches may be singular. The multiplier of the coset is c. -/
theorem exists_bijective_branch {m n : ℕ} (divides : m ∣ Fintype.card F-1)
    (phase : ¬m ∣ n) (size : Fintype.card E = Fintype.card F ^ n) (a : E) :
    ∃ c : Eˣ, Function.Bijective
      (fun x : E => ((c:E)^((Fintype.card E-1)/m))*x^Fintype.card F-a*x) := by
  classical
  let D := normExponent (Fintype.card F) n
  let e := (Fintype.card E-1)/m
  have hQ := normExponent_size size
  have hdvd : m ∣ Fintype.card E-1 := hQ ▸ dvd_mul_of_dvd_left divides D
  have hprod : e*m = Fintype.card E-1 := Nat.div_mul_cancel hdvd
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  have he : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero,zero_mul] at hprod
    exact (Nat.sub_pos_of_lt hq).ne' hprod.symm
  have hnD : ¬m ∣ D := fun hD => phase (Nat.modEq_zero_iff_dvd.1
    ((normExponent_modEq _ n m (Nat.le_of_lt Fintype.one_lt_card) divides).symm.trans hD.modEq_zero_nat))
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf g = Fintype.card E-1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,Fintype.card_units]
  have hζ : ((g:E)^e)^D ≠ 1 := by
    intro h
    have hu : (g ^ e) ^ D = 1 := Units.ext (by simpa using h)
    have ho := orderOf_dvd_of_pow_eq_one hu
    rw [orderOf_pow g,hord,← hprod,Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ he] at ho
    exact hnD ho
  have hex : ∃ c : Eˣ, a^D ≠ ((c:E)^e)^D := by
    by_cases ha : a^D = 1
    · exact ⟨g, by rw [ha]; exact Ne.symm hζ⟩
    · exact ⟨1, by simpa using ha⟩
  obtain ⟨c,hc⟩ := hex
  have hinj := branch_injective_of_norm_ne size ((c:E)^e) a hc
  exact ⟨c,hinj,Finite.surjective_of_injective hinj⟩

/-- All rational preimages of a singular branch are retained. Its fibre
over a rational value is empty or one affine line over the ground field. -/
theorem singular_fibre_card {n : ℕ} (hn : 0 < n)
    (size : Fintype.card E = Fintype.card F^n) (z a : Eˣ) (b : E)
    (same : (a:E)^normExponent (Fintype.card F) n = (z:E)^normExponent (Fintype.card F) n) :
    let X := {x:E // (z:E)*x^Fintype.card F-(a:E)*x=b}
    Nat.card X = 0 ∨ Nat.card X = Fintype.card F := by
  classical
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let r : E := (a:E)/(z:E)
  have hr : r ≠ 0 := div_ne_zero a.ne_zero z.ne_zero
  let L (x:E) := (z:E)*σ x-(a:E)*x
  have sub (x y:E) : L (x-y) = L x-L y := by simp only [L,map_sub]; ring
  have kernel (x:E) : L x = 0 ↔ σ x = r*x := by
    dsimp [L,r]
    rw [sub_eq_zero]
    constructor <;> intro h
    · apply mul_left_cancel₀ z.ne_zero
      rw [← mul_assoc,mul_div_cancel₀ _ z.ne_zero,h]
    · rw [h,← mul_assoc,mul_div_cancel₀ _ z.ne_zero]
  have noninj : ¬Function.Injective L := by
    simpa only [L,hσ] using mt (branch_injective_iff_norm_ne hn size z a).1 (not_not.mpr same)
  unfold Function.Injective at noninj
  push_neg at noninj
  obtain ⟨u,v,huv,hne⟩ := noninj
  let w := u-v
  have hw : w ≠ 0 := sub_ne_zero.mpr hne
  have hker : L w = 0 := by dsimp [w]; rw [sub,huv,sub_self]
  have hwσ := (kernel _).mp hker
  let X := {x:E // (z:E)*x^Fintype.card F-(a:E)*x=b}
  by_cases hx : Nonempty X
  · right
    obtain ⟨x₀,hx₀⟩ := hx.some
    have seed : L x₀ = b := by simpa only [L,hσ] using hx₀
    let coord (t:F) : E := x₀+algebraMap F E t*w
    have onto (x:E) : L x=b ↔ ∃ t:F, coord t=x := by
      constructor
      · intro hx'
        have hdiff : L (x-x₀) = 0 := by rw [sub,hx',seed,sub_self]
        have hfixed : σ ((x-x₀)/w) = (x-x₀)/w := by
          rw [map_div₀,(kernel _).mp hdiff,hwσ]; field_simp; ring
        obtain ⟨t,ht⟩ := (pow_card_eq_iff_scalar F E _).1 ((hσ _).symm.trans hfixed)
        refine ⟨t,?_⟩
        dsimp [coord]
        rw [ht,div_mul_cancel₀ _ hw]; ring
      · rintro ⟨t,rfl⟩
        have ht : L (algebraMap F E t*w) = 0 := (kernel _).mpr (by
          rw [map_mul,σ.commutes,hwσ]; ring)
        dsimp [coord]
        calc L (x₀+algebraMap F E t*w) = L x₀ + L (algebraMap F E t*w) := by
               simp only [L,map_add]; ring
             _ = b := by rw [seed,ht,add_zero]
    let mapTo (t:F) : X := ⟨coord t,by simpa only [L,hσ] using (onto _).2 ⟨t,rfl⟩⟩
    have hi : Function.Injective mapTo := by
      intro t t' he
      have hval : coord t = coord t' := congrArg Subtype.val he
      exact (algebraMap F E).injective (mul_right_cancel₀ hw (add_left_cancel hval))
    have hs : Function.Surjective mapTo := by
      rintro ⟨x,hx⟩
      have hx' : L x = b := by simpa only [L,hσ] using hx
      obtain ⟨t,ht⟩ := (onto x).1 hx'
      exact ⟨t,Subtype.ext ht⟩
    exact (Nat.card_congr (Equiv.ofBijective mapTo ⟨hi,hs⟩).symm).trans Nat.card_eq_fintype_card
  · left
    letI : IsEmpty X := not_nonempty_iff.mp hx
    exact Nat.card_of_isEmpty

/-- All cyclotomic multipliers of nonzero arguments lie in the given base
field and are actual m-th roots of unity there. -/
theorem cyclotomic_value_in_ground {m n : ℕ} (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) (x:E) (hx:x≠0) :
    ∃ z : Fˣ, z^m=1 ∧ algebraMap F E (z:F) = x^((Fintype.card E-1)/m) := by
  let s := Fintype.card F
  let e := (Fintype.card E-1)/m
  have hQ : m ∣ Fintype.card E-1 :=
    normExponent_size size ▸ dvd_mul_of_dvd_left divides (normExponent s n)
  have unitRoot : (x^e)^m = 1 := by
    rw [← pow_mul,show e*m=Fintype.card E-1 from Nat.div_mul_cancel hQ]
    exact FiniteField.pow_card_sub_one_eq_one x hx
  obtain ⟨j,hj⟩ := divides
  have hfix : (x^e)^s=x^e := by
    have he : s = m*j+1 := hj ▸ (Nat.sub_add_cancel (Nat.le_of_lt (Fintype.one_lt_card (α := F)))).symm
    rw [he,pow_succ,pow_mul,unitRoot,one_pow,one_mul]
  obtain ⟨u,hu⟩ := (pow_card_eq_iff_scalar F E _).1 hfix
  have hne : u≠0 := by intro h; rw [h,map_zero] at hu; exact (pow_ne_zero _ hx) hu.symm
  refine ⟨Units.mk0 u hne,?_,hu⟩
  apply Units.ext
  change u^m=1
  apply (algebraMap F E).injective
  rwa [map_pow,hu,map_one]

/-- When m divides the extension degree, every ground-field m-th root is
a Frobenius eigenvalue on a nonzero rational vector. -/
theorem exists_frobenius_eigenvector {m n : ℕ} (hn : 0<n) (phase : m ∣ n)
    (size : Fintype.card E = Fintype.card F^n) (z:Fˣ) (hz:z^m=1) :
    ∃ w:E, w≠0 ∧ w^Fintype.card F=algebraMap F E (z:F)*w := by
  let a := (Units.map (algebraMap F E).toMonoidHom) z
  have ha : (a:E)^normExponent (Fintype.card F) n = (1:E)^normExponent (Fintype.card F) n := by
    change (algebraMap F E (z:F))^normExponent (Fintype.card F) n = _
    rw [← map_pow,scalar_norm_power,one_pow]
    obtain ⟨j,rfl⟩ := phase
    have hz' : (z:F)^m = 1 := congrArg (fun u:Fˣ => (u:F)) hz
    rw [pow_mul,hz',one_pow,map_one]
  have noninj := mt (branch_injective_iff_norm_ne hn size (1:Eˣ) a).1 (not_not.mpr ha)
  unfold Function.Injective at noninj
  push_neg at noninj
  obtain ⟨u,v,h,hne⟩ := noninj
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  refine ⟨u-v,sub_ne_zero.mpr hne,?_⟩
  rw [← hσ,map_sub,hσ,hσ,mul_sub]
  change 1*u^Fintype.card F - algebraMap F E (z:F)*u =
    1*v^Fintype.card F - algebraMap F E (z:F)*v at h
  linear_combination h

/-- In the congruence class s = 1 mod m², the twist preserves each
multiplicative character value. Frobenius is injective on each class. -/
theorem twist_permutation_of_square_dvd {m n : ℕ} (hm : 0 < m)
    (divides : m^2 ∣ Fintype.card F-1) (size : Fintype.card E = Fintype.card F^n) :
    Function.Bijective (fun x:E => x^(Fintype.card F+(Fintype.card E-1)/m)) := by
  let s := Fintype.card F
  let q := Fintype.card E
  let e := (q-1)/m
  have hs : 1 < s := Fintype.one_lt_card
  have hQ : m*m ∣ q-1 := by
    rw [← normExponent_size size]
    exact dvd_mul_of_dvd_left (by simpa [sq] using divides) _
  obtain ⟨j,hj⟩ := hQ
  have he : e = m*j := by
    dsimp [e]
    rw [hj,Nat.mul_assoc,Nat.mul_div_cancel_left _ hm]
  have hprod : e*m = q-1 := by rw [he,hj]; ring
  have hbase : m ∣ s-1 := dvd_trans (by simp [sq]) divides
  obtain ⟨i,hi⟩ := hbase
  have hpos : 0 < s+e := Nat.add_pos_left Fintype.card_pos _
  have class_fixed (x:E) (hx:x≠0) : (x^(s+e))^e = x^e := by
    have hclass : (x^e)^m = 1 := by rw [← pow_mul,hprod]; exact FiniteField.pow_card_sub_one_eq_one _ hx
    have hexp : s+e = 1 + m*(i+j) := by rw [he,mul_add,← hi]; omega
    rw [← pow_mul,mul_comm,pow_mul,hexp,pow_add,pow_one,pow_mul,hclass,one_pow,mul_one]
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  have inj : Function.Injective (fun x:E => x^(s+e)) := by
    intro x y h
    change x^(s+e) = y^(s+e) at h
    by_cases hx : x = 0
    · rw [hx,zero_pow hpos.ne'] at h
      exact hx.trans (pow_eq_zero h.symm).symm
    by_cases hy : y = 0
    · rw [hy,zero_pow hpos.ne'] at h
      exact (hx (pow_eq_zero h)).elim
    have hxy : (x^(s+e))^e = (y^(s+e))^e := congrArg (·^e) h
    rw [class_fixed x hx,class_fixed y hy] at hxy
    rw [pow_add,pow_add,hxy] at h
    apply σ.injective
    rw [hσ,hσ]
    exact mul_right_cancel₀ (pow_ne_zero _ hy) h
  exact ⟨inj,Finite.surjective_of_injective inj⟩

/-- A slope of primitive base-field norm. Either every branch is bijective,
or the base field has precisely m+1 elements and exactly one branch is
singular. This single choice works for all rational intercepts and shifts. -/
theorem primitive_norm_slope {m n : ℕ} (hn : 0<n) (divides : m ∣ Fintype.card F-1)
    (size : Fintype.card E = Fintype.card F^n) :
    ∃ a:Eˣ,
      let good (z:Fˣ) := Function.Bijective (fun x:E => algebraMap F E (z:F)*x^Fintype.card F-(a:E)*x)
      (∀ z:Fˣ, z^m=1 → good z) ∨ (Fintype.card F=m+1 ∧ m.Coprime n ∧
        ∃! z:Fˣ, z^m=1 ∧ ¬good z) := by
  classical
  let s := Fintype.card F
  let D := normExponent s n
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have ho : orderOf g = s-1 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg,Fintype.card_units]
  obtain ⟨a,ha⟩ := norm_power_surjective hn size (g:F)
  have hD : 0 < D := normExponent_pos Fintype.card_pos hn
  have ha0 : a≠0 := by
    intro h
    change a^D=algebraMap F E (g:F) at ha
    rw [h,zero_pow hD.ne'] at ha
    exact g.ne_zero ((algebraMap F E).injective (ha.symm.trans (map_zero _).symm))
  refine ⟨Units.mk0 a ha0,?_⟩
  let good (z:Fˣ) := Function.Bijective
    (fun x:E => algebraMap F E (z:F)*x^s-a*x)
  have iff (z:Fˣ) : ¬good z ↔ z^n=g := by
    let uz := Units.map (algebraMap F E).toMonoidHom z
    have hi := branch_injective_iff_norm_ne hn size uz (Units.mk0 a ha0)
    change Function.Injective (fun x:E => algebraMap F E (z:F)*x^s-a*x) ↔
      a^D ≠ (algebraMap F E (z:F))^D at hi
    rw [ha,←map_pow,scalar_norm_power] at hi
    have hgood : good z ↔ Function.Injective (fun x:E => algebraMap F E (z:F)*x^s-a*x) :=
      ⟨fun h => h.1,fun h => ⟨h,Finite.surjective_of_injective h⟩⟩
    rw [hgood,hi,not_not]
    constructor
    · intro h; exact Units.ext (((algebraMap F E).injective h).symm)
    · intro h; exact congrArg (algebraMap F E) (congrArg (fun u:Fˣ => (u:F)) h).symm
  change (∀ z:Fˣ, z^m=1 → good z) ∨ _
  by_cases allGood : ∀ z:Fˣ, z^m=1 → good z
  · exact Or.inl allGood
  · push_neg at allGood
    obtain ⟨z,hz,hbad⟩ := allGood
    have hzn := (iff z).1 hbad
    have hd : s-1 ∣ m := ho ▸ orderOf_dvd_of_pow_eq_one
      (show g^m=1 by rw [←hzn,←pow_mul,mul_comm,pow_mul,hz,one_pow])
    have hm : m=s-1 := Nat.dvd_antisymm divides hd
    have horder : orderOf z = s-1 := Nat.dvd_antisymm
      (by simpa [s,Fintype.card_units] using (orderOf_dvd_card (x := z)))
      (by rw [←ho,←hzn]; exact orderOf_pow_dvd n)
    have hcop : m.Coprime n := by
      have eq := congrArg orderOf hzn
      rw [orderOf_pow z,horder,ho] at eq
      have hs : 1<s := Fintype.one_lt_card
      exact hm ▸ (Nat.div_eq_self.mp eq).resolve_left (Nat.sub_pos_of_lt hs).ne'
    have hp : (Nat.card Fˣ).Coprime n := by
      rw [Nat.card_eq_fintype_card,Fintype.card_units]; exact hm ▸ hcop
    refine Or.inr ⟨?_,hcop,z,⟨hz,hbad⟩,?_⟩
    · change s=m+1
      rw [hm,Nat.sub_add_cancel (Nat.le_of_lt Fintype.one_lt_card)]
    · intro y hy
      exact hp.pow_left_bijective.1 (((iff y).1 hy.2).trans hzn.symm)

open PencilSampling

/-- A whole multiplicative coset of size (q−1)/m survives, as does the
distinct value at zero. This count covers horizontal lines as well. -/
theorem branch_hit_count {m n : ℕ} (divides : m ∣ Fintype.card F-1)
    (phase : ¬m ∣ n) (size : Fintype.card E = Fintype.card F^n) (l : Lines E) :
    let e := (Fintype.card E-1)/m
    (missed (Fintype.card F+e) l).card + e + 1 ≤ Fintype.card E := by
  classical
  let s := Fintype.card F
  let e := (Fintype.card E-1)/m
  let a := (PencilSampling.coordinates l).1
  let b := (PencilSampling.coordinates l).2
  obtain ⟨c,hc⟩ := exists_bijective_branch divides phase size a
  let L (x:E) := (c:E)^e*x^s-a*x
  have hi : Function.Injective L := hc.1
  have hdvd : m ∣ Fintype.card E-1 :=
    normExponent_size size ▸ dvd_mul_of_dvd_left divides (normExponent s n)
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  let H := Subgroup.zpowers (g^m)
  have hH : Fintype.card H = e := by
    dsimp [H,e]
    rw [Fintype.card_zpowers,orderOf_pow g,orderOf_eq_card_of_forall_mem_zpowers hg,
      Fintype.card_units,Nat.gcd_eq_right hdvd]
  let arg (u : H) := (c:E)*((u.val : Eˣ):E)
  let out (u : H) := L (arg u)-b
  have nonzero (u : H) : arg u ≠ 0 := mul_ne_zero c.ne_zero u.val.ne_zero
  have classValue (u : H) : (arg u)^e = (c:E)^e := by
    have hu : u^e = 1 := hH ▸ pow_card_eq_one
    have hcast := congrArg (fun v:H => ((v.val:Eˣ):E)) hu
    change (((u.val:Eˣ):E))^e = 1 at hcast
    simp [arg,mul_pow,hcast]
  have form (u : H) : (arg u)^(s+e)-a*arg u-b = out u := by
    rw [pow_add,classValue, mul_comm ((arg u)^s)]
  have injective : Function.Injective out := by
    intro u v h
    have h1 := hi (sub_left_inj.mp h)
    exact Subtype.ext (Units.ext (mul_left_cancel₀ c.ne_zero h1))
  have pos : 0 < s := Fintype.card_pos
  have L0 : L 0 = 0 := by simp [L,zero_pow pos.ne']
  have absent : -b ∉ univ.image out := by
    rintro he
    obtain ⟨u,_,hu⟩ := mem_image.mp he
    have harg : L (arg u) = L 0 := by
      dsimp [out] at hu
      rw [L0]
      linear_combination hu
    exact nonzero u (hi harg)
  let I := univ.filter (Hits (s+e) l)
  have sub : insert (-b) (univ.image out) ⊆ I := by
    intro y hy
    apply mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hy with rfl | hy
    · exact ⟨0,by simp [a,b,zero_pow (by omega : s+e≠0)]⟩
    · obtain ⟨u,_,rfl⟩ := mem_image.mp hy
      exact ⟨arg u,form u⟩
  have hcount := card_le_card sub
  rw [card_insert_of_not_mem absent,card_image_of_injective _ injective,card_univ,hH] at hcount
  have parts := filter_card_add_filter_neg_card_eq_card (Hits (s+e) l) (s := (univ : Finset E))
  change I.card+(missed (s+e) l).card = (univ : Finset E).card at parts
  rw [card_univ] at parts
  change (missed (s+e) l).card+e+1 ≤ Fintype.card E
  omega

/-- The nondividing side of the dichotomy has an unconditional logarithmic
upper bound, uniformly in the subfield and the extension degree. -/
theorem nondividing_projective_upper {m n : ℕ} (hm : 2 ≤ m)
    (divides : m ∣ Fintype.card F-1) (phase : ¬m ∣ n)
    (size : Fintype.card E = Fintype.card F^n) :
    ∃ S : Finset E, ProjectiveBlocks (Fintype.card F + (Fintype.card E-1)/m) (S : Set E) ∧
      (S.card:ℝ) ≤ 2*m*Real.log (2*Fintype.card E)+1 := by
  let q := Fintype.card E
  let e := (q-1)/m
  let d := Fintype.card F+e
  let M := q-(e+1)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 2 ≤ d := le_trans (Fintype.one_lt_card (α := F)) (Nat.le_add_right _ _)
  have hmiss (l : Lines E) : (missed d l).card ≤ M := by
    have h := branch_hit_count divides phase size l
    change (missed d l).card+e+1 ≤ q at h
    dsimp only [M]; omega
  have hdvd : m ∣ q-1 := normExponent_size size ▸
    dvd_mul_of_dvd_left divides (normExponent (Fintype.card F) n)
  have he : e*m+1=q := by
    have hprod : e*m=q-1 := Nat.div_mul_cancel hdvd
    omega
  have heq : e+1 ≤ q := by
    have hdiv : e ≤ q-1 := Nat.div_le_self _ _
    omega
  have hsum : M+(e+1) = q := Nat.sub_add_cancel heq
  have hm0 : (0:ℝ)<m := Nat.cast_pos.mpr (by omega)
  have hrate : (0:ℝ)<1/m := one_div_pos.mpr hm0
  have hbound : (M:ℝ) ≤ q*Real.exp (-(1/(m:ℝ))) := by
    have h₁ : (M:ℝ)+((e:ℝ)+1) = q := by exact_mod_cast hsum
    have h₂ : (e:ℝ)*m+1 = q := by exact_mod_cast he
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hp : (q:ℝ)/m ≤ e+1 := (div_le_iff hm0).2 (by nlinarith only [h₂,hm1])
    have hfirst : (M:ℝ) ≤ q*(-(1/(m:ℝ))+1) := by
      rw [mul_add,mul_neg,mul_one_div,mul_one]
      linarith only [h₁,hp]
    exact hfirst.trans (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (Nat.cast_nonneg _))
  obtain ⟨S,hS,hcard⟩ := projective_split_upper (F := E) (ε := 0) hd hrate hrate le_rfl
    (by simpa using mul_nonneg hrate.le (Real.sqrt_nonneg (Fintype.card E)))
    (fun b => hmiss (.inl b)) (fun l => hmiss (.inr l)) hbound (by simpa using hbound)
  refine ⟨S,hS,hcard.trans ?_⟩
  have hq0 : (0:ℝ)<q := Nat.cast_pos.mpr (by omega)
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (Nat.le_of_lt hq))
  change sampleCutoff q (1/2) (1/(m:ℝ)) (1/(m:ℝ)) 0 + 1 ≤ 2*m*Real.log (2*q)+1
  simp only [sampleCutoff, Real.log_inv,Real.log_div one_ne_zero (by norm_num : (2:ℝ)≠0),Real.log_one,
    Real.log_mul (by norm_num : (2:ℝ)≠0) hq0.ne',zero_sub,sub_neg_eq_add,
    zero_div,mul_zero,add_zero,one_div,div_inv_eq_mul]
  apply add_le_add_right
  apply max_le
  · nlinarith only [mul_nonneg hlog hm0.le]
  · ring_nf; rfl

end BlockingCurves.ExtensionPhase
