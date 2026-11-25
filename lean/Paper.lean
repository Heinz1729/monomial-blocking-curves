import Frobenius
import Projective

namespace BlockingCurves
variable {E : Type*} [Field E]

/-- A numerical minimum on affine line tests is the same minimum for the
full homogeneous equations, including the line at infinity. -/
theorem projective_minimum_of_graph {d N : ℕ} (hd : 2 ≤ d)
    (h : IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧
      GraphHits (fun x : E => x ^ d) (S : Set E)} N) :
    IsLeast {r : ℕ | ∃ S : Finset E, S.card = r ∧ ProjectiveBlocks d (S : Set E)} N := by
  simpa only [projectiveBlocks_iff_graphHits hd] using h

/-- The minimum in AGY Question 5.4 for the projective Frobenius pencil. -/
theorem projective_prime_power_minimum (p h e : ℕ) [hp : Fact p.Prime]
    (hh : h ≠ 0) (he : e ≠ 0) :
    IsLeast {r : ℕ | ∃ S : Finset (GaloisField p h), S.card = r ∧
      ProjectiveBlocks (p ^ e) (S : Set (GaloisField p h))}
      ((p ^ (h.gcd e) - 1) * (h / h.gcd e) + 1) := by
  have hd : 2 ≤ p ^ e := by
    have hp1 := hp.out.one_lt
    exact Nat.one_lt_pow he hp1
  exact projective_minimum_of_graph hd (prime_power_frobenius_minimum p h e hh)

#print axioms projective_prime_power_minimum
end BlockingCurves

