import NormPencilTrace
import PhaseBranches
import PiecewiseNormPolynomial

/-! Norm spheres and the reciprocal equation for the Frobenius-degree cusp. -/
namespace BlockingCurves.CuspidalNorm

open Finset FiniteDimensional NormPencil
open scoped BigOperators

variable (F : Type*) {E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] [FiniteDimensional F E]

/-- Containment in a translated norm fibre of nonzero radius. -/
def OnSphere (S : Finset E) : Prop :=
  ∃ b : E, ∃ R : F, R ≠ 0 ∧ ∀ α ∈ S, Algebra.norm F (b+α) = R

/-- Affine slope-intercept condition for the parametrized cusp of degree |F|. -/
def Hits (S : Finset E) : Prop :=
  ∀ m b : E, ∃ t : E, t^(Fintype.card F) - m*t^(Fintype.card F-1)-b ∈ S

private theorem reciprocal {s : ℕ} (hs : 0<s) {t : E} (ht : t ≠ 0) (m z : E) :
    t^s - m*t^(s-1)=z ↔ z*(t⁻¹)^s + m*t⁻¹ = 1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  simp only [Nat.succ_sub_one, inv_pow]
  have p : t^(k+1) ≠ 0 := pow_ne_zero _ ht
  have e : t⁻¹ * t^(k+1) = t^k := by rw [pow_succ']; field_simp
  constructor
  · intro h
    apply mul_right_cancel₀ p
    rw [add_mul,mul_assoc,inv_mul_cancel p,mul_one,mul_assoc,e,one_mul]
    rw [Nat.succ_eq_add_one] at h
    linear_combination -h
  · intro h
    have eq := congrArg (fun x : E => x*t^(k+1)) h
    simp only [add_mul,mul_assoc,inv_mul_cancel p,mul_one,e,one_mul] at eq
    rw [Nat.succ_eq_add_one]
    linear_combination -eq

/-- A missed line forces all parameters onto one nonzero norm sphere. -/
theorem hits_of_no_sphere (S : Finset E) (notOn : ¬ OnSphere F S) : Hits F S := by
  classical
  have size : Fintype.card E = Fintype.card F ^ finrank F E := card_eq_pow_finrank
  have hs := Fintype.one_lt_card (α:=F)
  intro m b
  by_contra! miss
  refine notOn ⟨b,Algebra.norm F (-m),?_,?_⟩
  · by_contra hz
    have hm : m=0 := by simpa [Algebra.norm_eq_zero_iff] using hz
    obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
    have empty : S=∅ := eq_empty_iff_forall_not_mem.mpr (fun α h => by
      obtain ⟨t,ht⟩ := σ.surjective (b+α)
      apply miss t
      simpa [hm,← hσ,ht] using h)
    exact notOn ⟨0,1,one_ne_zero,by simp [empty]⟩
  · intro α hα
    by_contra ne
    let z := b+α
    have hp : (-m)^normExponent (Fintype.card F) (finrank F E) ≠
        z^normExponent (Fintype.card F) (finrank F E) := by
      simpa only [← norm_eq_power] using (algebraMap F E).injective.ne (Ne.symm ne)
    have inj := ExtensionPhase.branch_injective_of_norm_ne size z (-m) hp
    obtain ⟨v,hv⟩ := Finite.surjective_of_injective inj 1
    have hv' : z*v^(Fintype.card F)+m*v=1 := by simpa using hv
    have vn : v≠0 := by rintro rfl; simp [zero_pow (by omega : Fintype.card F≠0)] at hv'
    have eq := (reciprocal Fintype.card_pos (inv_ne_zero vn) m z).2 (by simpa using hv')
    apply miss v⁻¹
    rw [eq]
    simpa [z] using hα

private theorem singular_image_card (a z : Eˣ) (hsame : Algebra.norm F (a:E)=Algebra.norm F (z:E)) :
    open Classical in
    (univ.image (fun x:E => (z:E)*x^(Fintype.card F)-(a:E)*x)).card*(Fintype.card F)
      = Fintype.card E := by
  classical
  let L (x:E) := (z:E)*x^(Fintype.card F)-(a:E)*x
  have p : (a:E)^normExponent (Fintype.card F) (finrank F E) =
      (z:E)^normExponent (Fintype.card F) (finrank F E) := by
    simpa only [← norm_eq_power] using congrArg (algebraMap F E) hsame
  have fibre (y:E) (hy:y∈univ.image L) : (univ.filter fun x:E => L x=y).card = Fintype.card F := by
    obtain ⟨x,_,hx⟩ := mem_image.mp hy
    have h := ExtensionPhase.singular_fibre_card (F:=F) (E:=E) finrank_pos card_eq_pow_finrank z a y p
    have positive : 0 < Nat.card {v:E // L v=y} := by
      letI : Nonempty {v:E // L v=y} := ⟨⟨x,hx⟩⟩
      exact Nat.card_pos
    have card := h.resolve_left positive.ne'
    simpa only [Nat.card_eq_fintype_card,Fintype.card_subtype,L] using card
  have total := Finset.card_eq_sum_card_image L (univ : Finset E)
  rw [sum_congr rfl fibre] at total
  simpa [L] using total.symm

/-- Below |F| shifts, any common nonzero norm sphere supplies a missing line.
Its slope is chosen after excluding all the singular linear images. -/
theorem not_hits_of_sphere (S : Finset E) (small : S.card < Fintype.card F)
    (sphere : OnSphere F S) : ¬ Hits F S := by
  classical
  obtain ⟨b,R,hR,same⟩ := sphere
  intro hits
  obtain ⟨t,ht⟩ := hits 0 0
  let c := t^(Fintype.card F) - 0*t^(Fintype.card F-1) - 0
  have hc : c∈S := ht
  let a := b+c
  have ha : a≠0 := fun eq => hR (by rw [← same c hc,show b+c=0 from eq]; simp)
  let L (α x:E) := (b+α)*x^(Fintype.card F)-a*x
  let bad (α:E) := univ.image (L α)
  let U := S.biUnion bad
  have one (α:E) (h:α∈S) : (bad α).card ≤ Fintype.card E/Fintype.card F := by
    have nz : b+α≠0 := fun eq => hR (by rw [← same α h,eq];simp)
    exact (Nat.le_div_iff_mul_le Fintype.card_pos).mpr
      (singular_image_card F (Units.mk0 a ha) (Units.mk0 (b+α) nz)
        ((same c hc).trans (same α h).symm)).le
  have cb := card_biUnion_le_card_mul S bad (Fintype.card E / Fintype.card F) one
  have lt : U.card < Fintype.card E := by
    by_cases hz : Fintype.card E / Fintype.card F=0
    · rw [hz,mul_zero] at cb
      exact cb.trans_lt Fintype.card_pos
    · exact cb.trans_lt ((Nat.mul_lt_mul_of_pos_right small (Nat.pos_of_ne_zero hz)).trans_le
        ((Nat.mul_comm _ _) ▸ Nat.div_mul_le_self (Fintype.card E) (Fintype.card F)))
  obtain ⟨u,hu⟩ : ∃ u:E, u∉U := by
    by_contra! full
    rw [eq_univ_of_forall full,card_univ] at lt
    exact (lt_irrefl _) lt
  have hu0 : u≠0 := by
    rintro rfl
    apply hu (mem_biUnion.mpr ⟨c,hc,mem_image.mpr ⟨0,mem_univ _,?_⟩⟩)
    simp [L,zero_pow Fintype.card_pos.ne']
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  obtain ⟨k,hk⟩ := σ.surjective u
  have kpow : k^(Fintype.card F)=u := (hσ k).symm.trans hk
  let m := -(a*k)/u
  obtain ⟨x,hx⟩ := hits m b
  let α := x^(Fintype.card F)-m*x^(Fintype.card F-1)-b
  have mem : α∈S := hx
  have zne : b+α≠0 := fun eq => hR (by rw [← same α mem,eq];simp)
  have xne : x≠0 := by
    rintro rfl
    apply zne
    have h := Fintype.one_lt_card (α:=F)
    simp [α,zero_pow (by omega : Fintype.card F≠0),zero_pow (by omega : Fintype.card F-1≠0)]
  have hr := (reciprocal Fintype.card_pos xne m (b+α)).1 (by dsimp [α];ring)
  apply hu (mem_biUnion.mpr ⟨α,mem,mem_image.mpr ⟨k*x⁻¹,mem_univ _,?_⟩⟩)
  dsimp [L]
  rw [mul_pow,kpow]
  calc
    _ = ((b+α)*(x⁻¹)^(Fintype.card F)+m*x⁻¹)*u := by
      conv_rhs => rw [add_mul,show m*x⁻¹*u=(m*u)*x⁻¹ by ring,
        show m*u= -(a*k) from div_mul_cancel₀ _ hu0]
      ring
    _ = u := by rw [hr,one_mul]

theorem hits_iff_no_sphere (S : Finset E) (small : S.card < Fintype.card F) :
    Hits F S ↔ ¬ OnSphere F S :=
  ⟨fun hit sphere => not_hits_of_sphere F S small sphere hit, hits_of_no_sphere F S⟩

end BlockingCurves.CuspidalNorm
