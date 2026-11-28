import Projective

/-! Vertical translates of the rational curve parametrized by
    (t^(d-1), t^d), with its unique point at infinity. -/
namespace BlockingCurves.CuspidalGeneral

variable {F : Type*} [Field F]

/-- Blocking every projective line by the indicated homogeneous curves. -/
def Blocks (d : ℕ) (S : Set F) : Prop :=
  ∀ a b c : F, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) →
    ∃ α ∈ S, ∃ X Y Z : F, (X ≠ 0 ∨ Y ≠ 0 ∨ Z ≠ 0) ∧
      a*X+b*Y+c*Z=0 ∧ (Y+α*Z)^(d-1)*Z=X^d

theorem parametrization {d : ℕ} (hd : 2 ≤ d) (x y : F) (h : y^(d-1)=x^d) :
    ∃ t : F, t^(d-1)=x ∧ t^d=y := by
  obtain ⟨k,rfl⟩ : ∃ k, d=k+2 := ⟨d-2, by omega⟩
  change y^(k+1)=x^(k+2) at h
  by_cases hx : x=0
  · subst x
    have hy : y=0 := by simpa using h
    exact ⟨0,by simp,by simp [hy]⟩
  · have first : (y/x)^(k+1)=x := by
      rw [div_pow,div_eq_iff (pow_ne_zero _ hx),h,pow_succ x (k+1),mul_comm]
    exact ⟨y/x, first, by rw [pow_succ,first]; field_simp⟩

/-- The full projective test reduces to all affine slopes and intercepts. -/
theorem blocks_iff {d : ℕ} (hd : 2 ≤ d) (S : Set F) :
    Blocks d S ↔ ∀ m b : F, ∃ t : F, t^d-m*t^(d-1)-b ∈ S := by
  obtain ⟨k,rfl⟩ : ∃ k, d=k+2 := ⟨d-2, by omega⟩
  constructor
  · intro hs m b
    obtain ⟨α,hα,X,Y,Z,hn,hl,hc⟩ := hs (-m) 1 (-b) (Or.inr (Or.inl one_ne_zero))
    change (Y+α*Z)^(k+1)*Z=X^(k+2) at hc
    have hz : Z≠0 := by
      intro he
      subst Z
      have hx : X=0 := by simpa using hc.symm
      subst X
      have hy : Y=0 := by simpa using hl
      simp [hy] at hn
    have he : ((Y+α*Z)/Z)^(k+1)=(X/Z)^(k+2) := by
      rw [div_pow,div_pow,div_eq_div_iff (pow_ne_zero _ hz) (pow_ne_zero _ hz),
        pow_succ Z (k+1),← hc]
      ring
    obtain ⟨t,ht,ht'⟩ := parametrization (d:=k+2) (by omega) _ _ he
    refine ⟨t,?_⟩
    convert hα using 1
    rw [ht,ht']
    field_simp [hz]
    linear_combination hl
  · intro hs a b c _
    by_cases hb : b=0
    · obtain ⟨t,ht⟩ := hs 0 0
      exact ⟨_,ht,0,1,0,Or.inr (Or.inl one_ne_zero),by simp [hb],by simp⟩
    · let m := -a/b
      let v := -c/b
      obtain ⟨t,ht⟩ := hs m v
      refine ⟨_,ht,t^(k+1),m*t^(k+1)+v,1,Or.inr (Or.inr one_ne_zero),?_,?_⟩
      · dsimp [m,v]
        field_simp [hb]
        ring
      · change (_ + (t^(k+2)-m*t^(k+1)-v)*1)^(k+1)*1=(t^(k+1))^(k+2)
        simp only [mul_one]
        rw [show m*t^(k+1)+v+(t^(k+2)-m*t^(k+1)-v)=t^(k+2) by ring,
          ← pow_mul,← pow_mul,Nat.mul_comm]

/-- Both quadratic pencils have the same projective blocking sets, including
over the four-element field where the three shifts cannot all lie in F₂. -/
theorem degree_two_iff_graph (S : Set F) :
    Blocks 2 S ↔ ProjectiveBlocks 2 S := by
  rw [blocks_iff (by decide : 2 ≤ 2),projectiveBlocks_iff_graphHits (by decide : 2 ≤ 2)]
  simp only [GraphHits,show 2-1=1 by decide,pow_one]

end BlockingCurves.CuspidalGeneral
