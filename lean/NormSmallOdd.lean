import NormSmall
import Mathlib.Algebra.Field.MinimalAxioms

namespace BlockingCurves.NormPencil

private instance prime5 : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance prime7 : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance prime11 : Fact (Nat.Prime 11) := ⟨by decide⟩
private instance prime13 : Fact (Nat.Prime 13) := ⟨by decide⟩
private instance prime17 : Fact (Nat.Prime 17) := ⟨by decide⟩
private instance prime19 : Fact (Nat.Prime 19) := ⟨by decide⟩
private instance prime23 : Fact (Nat.Prime 23) := ⟨by decide⟩

/-- The compact lookup table is sound once checked on every nonzero square.
Every witness still has its discriminant recomputed using field arithmetic. -/
private theorem scalarCheck_mask {F : Type*} [Field F] {s : ℕ} (good : F → Bool)
    (hbad : ∀ u : F, u ≠ 0 → good (u^2) = false)
    (hgood : ∀ a : Fin (s-1), ∀ t j : F, j ≠ 0 →
      ∃ v : F, good ((t-v^(a.val+1))^2-4*(j*v)) = true) :
    ScalarCheck F s := by
  intro a t j hj
  obtain ⟨v,hv⟩ := hgood a t j hj
  refine ⟨v,fun u hu he => ?_⟩
  rw [← he,hbad u hu] at hv
  contradiction

private structure F9 where
  re : Fin 3
  im : Fin 3
  deriving DecidableEq

private def nineEquiv : F9 ≃ Fin 3 × Fin 3 :=
  ⟨fun a => (a.re,a.im), fun a => ⟨a.1,a.2⟩, fun _ => rfl, fun _ => rfl⟩
private instance : Fintype F9 := Fintype.ofEquiv _ nineEquiv.symm

private instance : Zero F9 := ⟨⟨0,0⟩⟩
private instance : One F9 := ⟨⟨1,0⟩⟩
private instance : Add F9 := ⟨fun x y => ⟨x.re+y.re,x.im+y.im⟩⟩
private instance : Neg F9 := ⟨fun x => ⟨-x.re,-x.im⟩⟩
private instance : Mul F9 := ⟨fun x y => ⟨x.re*y.re-x.im*y.im,x.re*y.im+x.im*y.re⟩⟩
private def conj (x : F9) : F9 := ⟨x.re,-x.im⟩
private instance : Inv F9 := ⟨fun x =>
  let n := x.re*x.re+x.im*x.im
  ⟨n*(conj x).re,n*(conj x).im⟩⟩
private instance : Field F9 := Field.ofMinimalAxioms F9 (by decide) (by decide) (by decide)
  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

set_option maxHeartbeats 2000000 in
private theorem check9 : ScalarCheck F9 9 := by
  apply scalarCheck_mask (fun z : F9 => !Nat.testBit 78 (z.re.val+3*z.im.val)) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check3 : ScalarCheck (ZMod 3) 3 := by
  apply scalarCheck_mask (fun z : ZMod 3 => !Nat.testBit 2 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check5 : ScalarCheck (ZMod 5) 5 := by
  apply scalarCheck_mask (fun z : ZMod 5 => !Nat.testBit 18 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check7 : ScalarCheck (ZMod 7) 7 := by
  apply scalarCheck_mask (fun z : ZMod 7 => !Nat.testBit 22 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check11 : ScalarCheck (ZMod 11) 11 := by
  apply scalarCheck_mask (fun z : ZMod 11 => !Nat.testBit 570 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check13 : ScalarCheck (ZMod 13) 13 := by
  apply scalarCheck_mask (fun z : ZMod 13 => !Nat.testBit 5658 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check17 : ScalarCheck (ZMod 17) 17 := by
  apply scalarCheck_mask (fun z : ZMod 17 => !Nat.testBit 107286 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check19 : ScalarCheck (ZMod 19) 19 := by
  apply scalarCheck_mask (fun z : ZMod 19 => !Nat.testBit 199410 z.val) <;> decide

set_option maxHeartbeats 4000000 in
private theorem check23 : ScalarCheck (ZMod 23) 23 := by
  apply scalarCheck_mask (fun z : ZMod 23 => !Nat.testBit 340830 z.val) <;> decide

/-- All positive exponents, all finite-field models of these orders, and all
scaled norm targets. Each finite test is checked by kernel reduction. -/
theorem small_odd_scalar_witness (F : Type*) [Field F] [Fintype F] {m : ℕ} (hm : 0<m)
    (hs : Fintype.card F ∈ ([3,5,7,9,11,13,17,19,23] : List ℕ)) : ScalarWitness F m := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h3|h5|h7|h9|h11|h13|h17|h19|h23
  · have hc : Fintype.card (ZMod 3) = 3 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h3.symm))
      (scalarWitness_of_check hc check3 hm)
  · have hc : Fintype.card (ZMod 5) = 5 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h5.symm))
      (scalarWitness_of_check hc check5 hm)
  · have hc : Fintype.card (ZMod 7) = 7 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h7.symm))
      (scalarWitness_of_check hc check7 hm)
  · have hc : Fintype.card (F9) = 9 := by decide
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h9.symm))
      (scalarWitness_of_check hc check9 hm)
  · have hc : Fintype.card (ZMod 11) = 11 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h11.symm))
      (scalarWitness_of_check hc check11 hm)
  · have hc : Fintype.card (ZMod 13) = 13 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h13.symm))
      (scalarWitness_of_check hc check13 hm)
  · have hc : Fintype.card (ZMod 17) = 17 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h17.symm))
      (scalarWitness_of_check hc check17 hm)
  · have hc : Fintype.card (ZMod 19) = 19 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h19.symm))
      (scalarWitness_of_check hc check19 hm)
  · have hc : Fintype.card (ZMod 23) = 23 := ZMod.card _
    exact scalarWitness_transport (FiniteField.ringEquivOfCardEq (hc.trans h23.symm))
      (scalarWitness_of_check hc check23 hm)

end BlockingCurves.NormPencil
