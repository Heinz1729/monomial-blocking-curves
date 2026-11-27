import NormCubicTrace
import NormPencilTrace

/-! Exact projective minimum for all powers of the norm in a cubic extension. -/
namespace BlockingCurves.NormPencil

variable {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
  [Algebra F E] [FiniteDimensional F E]

/-- For every cubic extension, a horizontal optimum lifts to a full pencil
of minimum size. This includes all base fields and all positive powers. -/
theorem cubic_extension_norm_minimum (hn : FiniteDimensional.finrank F E = 3)
    {m : ℕ} (hm : 0 < m) :
    AsgarliGhiocaYip.isPencilMinimum E (m * normExponent (Fintype.card F) 3)
      ((Fintype.card F)^2 * coverNumber F m) := by
  simpa [hn] using minimum_of_trace_zero_norm (by omega : 2 ≤ FiniteDimensional.finrank F E)
    hm (exists_trace_zero_norm F E hn)

end BlockingCurves.NormPencil
