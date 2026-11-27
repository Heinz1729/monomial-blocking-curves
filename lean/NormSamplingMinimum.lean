import NormPencilField
import NormCosetCover
import NormQuadraticCollision
import Frobenius

/-! Exact projective minima from the independent shifts in norm-power pencils. -/
namespace BlockingCurves.NormPencil
attribute [local instance] Classical.propDecidable
noncomputable section
variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
local instance : DecidableEq E := Classical.decEq _

private theorem norm_minimum_of_shifts {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n)
    (hbad : ∀ (π : E →ₗ[F] F), (∀ v : F, π (algebraMap F E v) = v) →
      (∑ j : Fˣ × E, ∏ z : LinearMap.ker π, (Fintype.card F -
        (slice π (target (m * normExponent (Fintype.card F) n) j) z).card)) <
      Fintype.card F ^ Fintype.card (LinearMap.ker π)) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) n)
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  classical
  have hd := (normExponent_two_le (s := Fintype.card F) Fintype.one_lt_card hn).trans
    (Nat.le_mul_of_pos_left _ hm)
  apply (AGY_minimum_iff hd _).2
  obtain ⟨π,split⟩ := exists_projection F E
  obtain ⟨T,ht,hT⟩ := coverNumber_attained F m
  have hpos : 0 < n := by omega
  obtain ⟨S,hc,hG⟩ := shifted_covers π split T hT (d := m * normExponent (Fintype.card F) n)
    (fun v => by
      obtain ⟨x,hx⟩ := norm_power_surjective hpos size v
      exact ⟨x,by rw [Nat.mul_comm, pow_mul, hx, map_pow]⟩)
    (fun x => by
      obtain ⟨v,hv⟩ := norm_in_ground hpos size x
      exact ⟨v^m,by rw [Nat.mul_comm, pow_mul, map_pow, hv]⟩)
    (hbad π split)
  constructor
  · exact ⟨S,hc.trans (by rw [cap_count π hpos split size, ht]),
      (projectiveBlocks_iff_graphHits hd _).2 hG⟩
  · rintro _ ⟨A,rfl,hA⟩
    apply norm_horizontal_lower hpos size A
    intro b
    simpa using (projectiveBlocks_iff_graphHits hd _).1 hA 0 b

/-- All dimensions at least four, with no restriction on the characteristic,
the base cardinality, or the positive exponent m. -/
theorem high_rank_norm_minimum {n m : ℕ} (hn : 4 ≤ n) (hm : 0 < m)
    (size : Fintype.card E = Fintype.card F ^ n) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) n)
      (Fintype.card F ^ (n-1) * coverNumber F m) := by
  classical
  apply norm_minimum_of_shifts (by omega : 2 ≤ n) hm size
  intro π split
  have hgr (x : E) : ∃ v : F, algebraMap F E v = x^(m * normExponent (Fintype.card F) n) := by
    obtain ⟨v,hv⟩ := norm_in_ground (by omega : 0 < n) size x
    exact ⟨v^m,by rw [Nat.mul_comm, pow_mul, map_pow, hv]⟩
  apply sparse_bad_count π hgr
  rw [cap_count π (by omega : 0 < n) split size, size]
  exact sparse_threshold Fintype.one_lt_card hn

/-- Quadratic rank, uniformly for every s≥25. The bound on the target size
is proved from the two-circle intersection calculation over the actual extension. -/
theorem large_quadratic_norm_minimum {m : ℕ} (hm : 0 < m) (hs : 25 ≤ Fintype.card F)
    (size : Fintype.card E = Fintype.card F ^ 2) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) 2)
      (Fintype.card F ^ (2-1) * coverNumber F m) := by
  classical
  apply norm_minimum_of_shifts (by decide : 2 ≤ 2) hm size
  intro π split
  apply dense_bad_count π split _ hs rfl size (by simpa using cap_count π (by decide : 0 < 2) split size)
  intro j
  let N (x : E) := Classical.choose (norm_in_ground (by decide : 0 < 2) size x)
  have hN (x : E) : algebraMap F E (N x) = x^normExponent (Fintype.card F) 2 :=
    Classical.choose_spec (norm_in_ground (by decide : 0 < 2) size x)
  obtain ⟨σ,hσ⟩ := exists_card_frobenius F E
  let φ (v : F) := (j.1:F)*v^m
  let g (x : E) := algebraMap F E (φ (N x)) - (1:E)*x
  have hd := NormQuadraticCollision.quadratic_value_density σ.toRingEquiv.toRingHom N
    (fun x => by
      change algebraMap F E (N x) = x * σ x
      rw [hN, hσ]; simp [normExponent, pow_succ', pow_add])
    φ (1:E) one_ne_zero size
  have ht : target (m * normExponent (Fintype.card F) 2) j =
      (Finset.univ.image g).image (fun v => v-j.2) := by
    unfold target
    rw [Finset.image_image]
    congr 1
    funext x
    simp only [Function.comp_apply, g, φ, map_mul, map_pow, hN, one_mul]
    rw [Nat.mul_comm m, pow_mul]
  rw [ht, Finset.card_image_of_injective _ (show Function.Injective (fun v : E => v-j.2) from fun _ _ he => sub_left_inj.mp he)]
  exact hd

end
end BlockingCurves.NormPencil
