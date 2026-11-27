import PhaseBranches

/-! Coefficient comparison for conjugates of inverse cyclotomic branches.
Dedekind independence isolates the quadratic norm obstruction. -/
namespace BlockingCurves.ExtensionPhase
open Finsupp

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

private theorem compare_two_terms (σ τ : E ≃ₐ[F] E) (hσ : σ ≠ 1)
    (a c z η : E) (ha : a ≠ 0) (hη : η ≠ 0)
    (identity : ∀ y:E, η*σ y - a*y = z*σ c*(σ*τ) y - a*c*τ y) :
    (τ=1 ∧ c=1 ∧ η=z) ∨ (τ=σ ∧ σ^2=1 ∧ η = -(a*c) ∧ z*σ c = -a) := by
  classical
  let G := E ≃ₐ[F] E
  let W (g:G) := (g:E → E)
  have li : LinearIndependent E W := (linearIndependent_monoidHom E E).comp
    (fun g:G => g.toAlgHom.toMonoidHom) (fun _ _ h => AlgEquiv.ext (fun x =>
      congrArg (fun f:E →* E => f x) h))
  have eq : (single σ η - single (1:G) a : G →₀ E) =
      single (σ*τ) (z*σ c) - single τ (a*c) := by
    apply (LinearMap.ker_eq_bot.mp li)
    simp only [map_sub,Finsupp.total_single]
    exact funext identity
  have coeff (g:G) := congrArg (fun l:G →₀ E => l g) eq
  by_cases ht : τ=1
  · subst τ
    have h1 := coeff 1
    have h2 := coeff σ
    simp [Finsupp.single_apply,hσ,hσ.symm] at h1 h2
    have hc : c=1 := by apply mul_left_cancel₀ ha; simpa using h1.symm
    exact Or.inl ⟨rfl,hc,by simpa [hc] using h2⟩
  · have hprod : σ*τ=1 := by
      by_contra ne
      have h := coeff 1
      simp [Finsupp.single_apply,hσ,ht,ne,hσ.symm,Ne.symm ht,Ne.symm ne,ha] at h
    have hsame : τ=σ := by
      by_contra ne
      have h := coeff σ
      simp [Finsupp.single_apply,hσ,hprod,ne,hσ.symm,Ne.symm ne,hη] at h
    have h1 := coeff 1
    have h2 := coeff σ
    rw [hprod] at h1 h2
    simp [Finsupp.single_apply,hσ,hsame,hσ.symm] at h1 h2
    exact Or.inr ⟨hsame,by simpa [sq,hsame] using hprod,h2,h1.symm⟩

/-- Only equal multipliers and equal conjugates can be proportional. In
degree two the forbidden scalar is exactly a times its Frobenius conjugate. -/
theorem inverse_branch_conjugates_rigid (σ ρ τ : E ≃ₐ[F] E) (hσ : σ≠1)
    (a:E) (ha:a≠0) (z η:F) (hη:η≠0)
    (noSwap : σ^2=1 → a*σ a ≠ algebraMap F E (z*η))
    (A B : E ≃ E)
    (hA : ∀ x:E, algebraMap F E z*σ (A x)-a*A x=x)
    (hB : ∀ x:E, algebraMap F E η*σ (B x)-a*B x=x)
    (c:E) (prop : ∀ x:E, ρ (A x) = c * τ (B x)) :
    ρ=τ ∧ z=η := by
  let k := ρ.symm * τ
  let b := ρ.symm c
  have hj (x:E) : A x = b*k (B x) := by
    have h := congrArg (fun y:E => ρ.symm y) (prop x)
    simpa [k,b,AlgEquiv.mul_apply] using h
  have identity (y:E) : algebraMap F E η*σ y-a*y =
      algebraMap F E z*σ b*(σ*k) y-a*b*k y := by
    have h := (hB (B.symm y)).trans (hA (B.symm y)).symm
    simpa only [hj,B.apply_symm_apply,map_mul,AlgEquiv.mul_apply,mul_assoc] using h
  rcases compare_two_terms σ k hσ a b (algebraMap F E z) (algebraMap F E η)
      ha (by simpa using (algebraMap F E).injective.ne hη) identity with good | bad
  · obtain ⟨hk,_,hz⟩ := good
    refine ⟨?_,(algebraMap F E).injective hz.symm⟩
    ext x
    have h := congrArg (fun g:E ≃ₐ[F] E => ρ (g x)) hk
    simpa [k,AlgEquiv.mul_apply] using h.symm
  · obtain ⟨_,hs,hηb,hzb⟩ := bad
    apply (noSwap hs _).elim
    have conjugate := congrArg (fun x:E => σ x) hηb
    change σ (algebraMap F E η) = σ (-(a*b)) at conjugate
    rw [σ.commutes,map_neg,map_mul] at conjugate
    rw [map_mul,conjugate]
    linear_combination (σ a)*hzb

/-- The bounded-degree norm slice, with actual inverse linear branches
indexed by the m-th roots. Distinct Frobenius conjugates are nonproportional,
uniformly over all finite base fields with the indicated norm condition. -/
theorem frobenius_inverse_conjugates [Fintype F] [Fintype E] [FiniteDimensional F E]
    {m : ℕ} (hn : 2 ≤ FiniteDimensional.finrank F E) (a:Eˣ)
    (avoid : ((a:E)^NormPencil.normExponent (Fintype.card F) (FiniteDimensional.finrank F E))^m ≠ 1) :
    let roots := {u : Fˣ // u^m=1}
    ∃ (σ : E ≃ₐ[F] E) (A : roots → E ≃ₗ[F] E),
      (∀ x:E, σ x = x^Fintype.card F) ∧
      (∀ (z:roots) (x:E), algebraMap F E (z.val:F)*σ (A z x)-(a:E)*A z x=x) ∧
      ∀ (z η:roots) (i j:Fin (FiniteDimensional.finrank F E)) (c:E),
        (∀ x:E, (σ^i.val) (A z x)=c*(σ^j.val) (A η x)) → z=η ∧ i=j := by
  classical
  let n := FiniteDimensional.finrank F E
  let D := NormPencil.normExponent (Fintype.card F) n
  let R := {u : Fˣ // u^m=1}
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let L (z:R) : E →ₗ[F] E := (z.val:F) • σ.toLinearEquiv.toLinearMap - LinearMap.mulLeft F (a:E)
  have Lval (z:R) (x:E) : L z x = algebraMap F E (z.val:F)*σ x-(a:E)*x := by
    simp [L,Algebra.smul_def]
  have root (z:R) : (algebraMap F E (z.val:F))^m=1 := by
    have h : (z.val:F)^m=1 := congrArg (fun u:Fˣ => (u:F)) z.property
    rw [← map_pow,h,map_one]
  have inj (z:R) : Function.Injective (L z) := by
    have diff : (a:E)^D ≠ (algebraMap F E (z.val:F))^D := by
      intro h
      apply avoid
      change ((a:E)^D)^m=1
      rw [h,← pow_mul,mul_comm,pow_mul,root,one_pow]
    simpa only [Function.Injective,Lval,hσ] using branch_injective_of_norm_ne
      (card_eq_pow_finrank (K := F) (V := E)) (algebraMap F E (z.val:F)) (a:E) diff
  let A (z:R) := (LinearEquiv.ofBijective (L z) ⟨inj z,Finite.surjective_of_injective (inj z)⟩).symm
  have rightInv (z:R) (x:E) : algebraMap F E (z.val:F)*σ (A z x)-(a:E)*A z x=x := by
    rw [← Lval]
    exact (A z).symm_apply_apply x
  have ho : orderOf σ = n := relative_order σ hσ
  have hne : σ≠1 := by
    intro h
    have : n=1 := by simpa [h] using ho.symm
    exact (Nat.ne_of_gt hn) this
  refine ⟨σ,A,hσ,rightInv,?_⟩
  intro z η i j c prop
  have exc (hsq:σ^2=1) : (a:E)*σ (a:E) ≠ algebraMap F E ((z.val:F)*(η.val:F)) := by
    have hdiv := orderOf_dvd_of_pow_eq_one hsq
    have hd : n=2 := le_antisymm (ho ▸ Nat.le_of_dvd (by decide) hdiv) hn
    intro he
    apply avoid
    change ((a:E)^NormPencil.normExponent (Fintype.card F) n)^m=1
    rw [hd]
    have hpow : (a:E)^NormPencil.normExponent (Fintype.card F) 2=(a:E)*σ (a:E) := by
      simp [NormPencil.normExponent,hσ,pow_add]
    rw [hpow,he,map_mul,mul_pow,root,root,one_mul]
  obtain ⟨h₁,h₂⟩ := inverse_branch_conjugates_rigid σ (σ^i.val) (σ^j.val) hne (a:E) a.ne_zero
    (z.val:F) (η.val:F) η.val.ne_zero exc (A z).toEquiv (A η).toEquiv
    (rightInv z) (rightInv η) c prop
  exact ⟨Subtype.ext (Units.ext h₂), Fin.ext (pow_injOn_Iio_orderOf
    (show i.val < orderOf σ from ho ▸ i.isLt) (show j.val < orderOf σ from ho ▸ j.isLt) h₁)⟩

end BlockingCurves.ExtensionPhase
