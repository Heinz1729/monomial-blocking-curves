import Cubic47Symmetry
import Cubic47Semantics

namespace BlockingCurves.Cubic47
open CubicPencil47

private def residueSet (A : List ℕ) : Set F := {s | s.val ∈ A}

private theorem rowValue (x m b : ℕ) :
    ((x : F)^3 + (m:F)*(x:F) + (b:F)).val = (x*x*x+m*x+b)%47 := by
  calc
    _ = ((↑(x*x*x+m*x+b) : F)).val := by congr 1; push_cast; ring
    _ = _ := ZMod.val_natCast _

private theorem residueSet_iff (A : List ℕ) :
    GraphHits (fun x : F => x^3) (residueSet A) ↔
      ∀ m ∈ residues, ∀ b ∈ residues, ∃ x ∈ residues, (x*x*x+m*x+b)%47 ∈ A := by
  constructor
  · intro h m _ b _
    obtain ⟨x,hx⟩ := h (-(m:F)) (-(b:F))
    refine ⟨x.val, List.mem_range.mpr x.val_lt, ?_⟩
    rw [← rowValue, ZMod.natCast_zmod_val]
    change (x^3 - -(m:F)*x - -(b:F)).val ∈ A at hx
    simpa [neg_mul] using hx
  · intro h m b
    obtain ⟨x, _, hx⟩ := h (-m).val (List.mem_range.mpr (ZMod.val_lt _))
      (-b).val (List.mem_range.mpr (ZMod.val_lt _))
    refine ⟨(x:F), ?_⟩
    rw [← rowValue, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at hx
    change ((x:F)^3 - m*(x:F) - b).val ∈ A
    simpa [sub_eq_add_neg, neg_mul] using hx

private theorem fourSet (u v : F) :
    residueSet [0,1,u.val,v.val] = (({0,1,u,v} : Finset F) : Set F) := by
  ext x
  change (x.val ∈ [0,1,u.val,v.val]) ↔ x ∈ ({0,1,u,v} : Finset F)
  simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton]
  change (x.val = (0:F).val ∨ x.val = (1:F).val ∨ x.val = u.val ∨ x.val = v.val) ↔ _
  simp only [(ZMod.val_injective 47).eq_iff]

private theorem noFour (S : Finset F) (hcard : S.card = 4)
    (hs : GraphHits (fun x : F => x^3) (S : Set F)) : False := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  obtain ⟨V,hV,h0,h1,hh⟩ := normalize S hs ha hb hab.symm
  let W := (V.erase 0).erase 1
  have h1' : 1 ∈ V.erase 0 := Finset.mem_erase.mpr ⟨one_ne_zero, h1⟩
  have hw : W.card = 2 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem h1', Finset.card_erase_of_mem h0, hV, hcard]
  obtain ⟨u,v,hne,hw'⟩ := Finset.card_eq_two.mp hw
  have huv : u.val ≠ v.val := fun he => hne ((ZMod.val_injective 47) he)
  have ord : ∃ i j : F, i.val < j.val ∧ W = {i,j} := by
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨u,v,h,hw'⟩
    · exact ⟨v,u,h,hw'.trans (Finset.pair_comm _ _)⟩
  obtain ⟨i,j,hij,hW⟩ := ord
  have hi : i ∈ W := by simp [hW]
  have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hi1 := (Finset.mem_erase.mp hi).1
  have hi0' : i.val ≠ 0 := fun he => hi0 ((ZMod.val_injective 47) (show i.val=(0:F).val from he))
  have hi1' : i.val ≠ 1 := fun he => hi1 ((ZMod.val_injective 47) (show i.val=(1:F).val from he))
  have he : V = {0,1,i,j} := by
    rw [← Finset.insert_erase h0, ← Finset.insert_erase h1', ← hW]
  apply no_four_witness (u := i.val) (v := j.val) (by omega) hij j.val_lt
  apply (normalized_iff [i.val,j.val]).mpr
  apply (residueSet_iff _).mp
  rwa [fourSet, ← he]

private theorem fiveSet :
    residueSet [0,1,3,15,33] = (({0,1,3,15,33} : Finset F) : Set F) := by
  ext x
  change (x.val ∈ [0,1,3,15,33]) ↔ x ∈ ({0,1,3,15,33} : Finset F)
  simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton]
  change (x.val = (0:F).val ∨ x.val = (1:F).val ∨ x.val = (3:F).val ∨
    x.val = (15:F).val ∨ x.val = (33:F).val) ↔ _
  simp only [(ZMod.val_injective 47).eq_iff]

theorem five_blocks : GraphHits (fun x : F => x^3) (({0,1,3,15,33} : Finset F) : Set F) := by
  rw [← fiveSet]
  exact (residueSet_iff _).mpr ((normalized_iff [3,15,33]).mp five_witness)

private theorem orderedTriple (u v w : F) (hab : u ≠ v) (hac : u ≠ w) (hbc : v ≠ w) :
    ∃ i j k : F, i.val < j.val ∧ j.val < k.val ∧
      ({u,v,w} : Finset F) = {i,j,k} := by
  have h₁ : u.val ≠ v.val := fun h => hab ((ZMod.val_injective 47) h)
  have h₂ : u.val ≠ w.val := fun h => hac ((ZMod.val_injective 47) h)
  have h₃ : v.val ≠ w.val := fun h => hbc ((ZMod.val_injective 47) h)
  rcases lt_or_gt_of_ne h₁ with h|h <;> rcases lt_or_gt_of_ne h₂ with he|he <;>
    rcases lt_or_gt_of_ne h₃ with hh|hh
  all_goals first
    | omega
    | exact ⟨u,v,w,by omega,by omega,rfl⟩
    | exact ⟨u,w,v,by omega,by omega,by ext; simp [or_assoc, or_left_comm, or_comm]⟩
    | exact ⟨v,u,w,by omega,by omega,by ext; simp [or_assoc, or_left_comm, or_comm]⟩
    | exact ⟨v,w,u,by omega,by omega,by ext; simp [or_assoc, or_left_comm, or_comm]⟩
    | exact ⟨w,u,v,by omega,by omega,by ext; simp [or_assoc, or_left_comm, or_comm]⟩
    | exact ⟨w,v,u,by omega,by omega,by ext; simp [or_assoc, or_left_comm, or_comm]⟩

def normalizedSets : List (Finset F) :=
  representativeTriples.map fun t => {0,1,(t.1 : F),(t.2.1 : F),(t.2.2 : F)}

/-- All normalized five-member blocking families over F₄₇. -/
theorem normalized_five (V : Finset F) (hcard : V.card = 5) (h0 : 0 ∈ V) (h1 : 1 ∈ V)
    (hh : GraphHits (fun x : F => x^3) (V : Set F)) :
    V ∈ normalizedSets := by
  let W := (V.erase 0).erase 1
  have h1' : 1 ∈ V.erase 0 := Finset.mem_erase.mpr ⟨one_ne_zero, h1⟩
  have hw : W.card = 3 := by
    dsimp [W]
    rw [Finset.card_erase_of_mem h1', Finset.card_erase_of_mem h0, hcard]
  obtain ⟨u,v,w,h₁,h₂,h₃,hw'⟩ := Finset.card_eq_three.mp hw
  obtain ⟨i,j,k,hij,hjk,ho⟩ := orderedTriple u v w h₁ h₂ h₃
  have hW := hw'.trans ho
  have hi : i ∈ W := by simp [hW]
  have hi0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
  have hi1 := (Finset.mem_erase.mp hi).1
  have hi0' : i.val ≠ 0 := fun he => hi0 ((ZMod.val_injective 47) (show i.val=(0:F).val from he))
  have hi1' : i.val ≠ 1 := fun he => hi1 ((ZMod.val_injective 47) (show i.val=(1:F).val from he))
  have hV : V = {0,1,i,j,k} := by
    rw [← Finset.insert_erase h0, ← Finset.insert_erase h1', ← hW]
  have lr : residueSet [0,1,i.val,j.val,k.val] = (V : Set F) := by
    rw [hV]
    ext x
    change (x.val ∈ [0,1,i.val,j.val,k.val]) ↔ x ∈ ({0,1,i,j,k} : Finset F)
    simp only [List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton]
    change (x.val=(0:F).val ∨ x.val=(1:F).val ∨ x.val=i.val ∨ x.val=j.val ∨ x.val=k.val) ↔ _
    simp only [(ZMod.val_injective 47).eq_iff]
  have hm := (five_witness_iff (u:=i.val) (v:=j.val) (w:=k.val) (by omega) hij hjk k.val_lt).mp
    ((normalized_iff [i.val,j.val,k.val]).mpr ((residueSet_iff _).mp (lr.symm ▸ hh)))
  apply List.mem_map.mpr
  refine ⟨(i.val,j.val,k.val), hm, ?_⟩
  simpa only [ZMod.natCast_zmod_val] using hV.symm

/-- The global minimum is five for the cubic pencil over F₄₇, with the
homogeneous projective incidence predicate (no normalization assumption). -/
theorem projective_cubic_minimum :
    IsLeast {r : ℕ | ∃ S : Finset F, S.card = r ∧ ProjectiveBlocks 3 (S : Set F)} 5 := by
  constructor
  · refine ⟨{0,1,3,15,33}, by decide, (projectiveBlocks_iff_graphHits (by decide) _).mpr ?_⟩
    rw [← fiveSet]
    exact (residueSet_iff _).mpr ((normalized_iff [3,15,33]).mp five_witness)
  · rintro r ⟨S, rfl, h⟩
    by_contra! hlt
    have hmono : 4-S.card+S.card ≤ (Finset.univ : Finset F).card := by
      have h47 : (Finset.univ : Finset F).card = 47 := by decide
      omega
    obtain ⟨V, hSV, _, hcard⟩ := Finset.exists_intermediate_set (4-S.card) hmono (Finset.subset_univ S)
    apply noFour V (by omega)
    intro m b
    obtain ⟨x, hx⟩ := ((projectiveBlocks_iff_graphHits (by decide) _).mp h) m b
    exact ⟨x, hSV hx⟩

#print axioms projective_cubic_minimum
end BlockingCurves.Cubic47
