import XRay.Blocks
import XRay.Compression

namespace XRay

 theorem left_anchor_assignments {m : ℕ} (hm : 0 < m) {A : Profile m}
    (hA : Realizable A) (hmin : A ⟨0, hm⟩ ≤ 2) :
    ∃ r c : Equiv.Perm (Fin m), (∀ i, A i = (r i).val + (c i).val + (1 : ℤ)) ∧
      r ⟨0, hm⟩ = ⟨0, hm⟩ := by
  obtain ⟨r, c, hrc⟩ := hA
  have hh := hrc ⟨0, hm⟩
  by_cases hr : (r ⟨0, hm⟩).val = 0
  · exact ⟨r, c, hrc, Fin.ext hr⟩
  · exact ⟨c, r, (fun i => by rw [hrc i]; ring),
      Fin.ext (show (c ⟨0, hm⟩).val = 0 by omega)⟩

 theorem right_anchor_assignments {m : ℕ} (hm : 0 < m) {A : Profile m}
    (hA : Realizable A) (hmax : 2 * (m : ℤ) - 2 ≤ A ⟨m - 1, by omega⟩) :
    ∃ r c : Equiv.Perm (Fin m), (∀ i, A i = (r i).val + (c i).val + (1 : ℤ)) ∧
      c ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := by
  obtain ⟨r, c, hrc⟩ := hA
  let j : Fin m := ⟨m - 1, by omega⟩
  have hh := hrc j
  have hrb := (r j).isLt
  have hcb := (c j).isLt
  by_cases hc : (c j).val = m - 1
  · exact ⟨r, c, hrc, Fin.ext hc⟩
  · exact ⟨c, r, (fun i => by rw [hrc i]; ring),
      Fin.ext (show (r j).val = m - 1 by change _ ≤ A j at hmax; omega)⟩

/-- Independent block transpositions supply the two compression anchors. -/
theorem compress_blocks {a b : ℕ} {A : Profile (a + 1)} {B : Profile (b + 1)}
    (hA : Realizable A) (hB : Realizable B)
    (hmin : A 0 ≤ 2) (hmax : 2 * (b : ℤ) ≤ B (Fin.last b)) :
    Realizable (compressExtremes (m := (a + 1) + b) (append (m := a + 1) (n := b + 1) A B)) := by
  obtain ⟨r, c, hrc, hr⟩ := left_anchor_assignments (by omega : 0 < a + 1) hA hmin
  have hmax' : 2 * ((b + 1 : ℕ) : ℤ) - 2 ≤ B ⟨b + 1 - 1, by omega⟩ := by
    change 2 * ((b + 1 : ℕ) : ℤ) - 2 ≤ B (Fin.last b)
    push_cast
    linarith
  obtain ⟨u, v, huv, hv⟩ := right_anchor_assignments (by omega : 0 < b + 1) hB hmax'
  apply compress_with_anchors (m := (a + 1) + b) (blockPerm (m := a + 1) (n := b + 1) r u) (blockPerm (m := a + 1) (n := b + 1) c v)
  · intro i
    refine Fin.addCases (m := a + 1) (n := b + 1) (fun j => ?_) (fun j => ?_) i
    · simp only [append, Fin.addCases_left, blockPerm_left, Fin.val_castAdd, hrc]
    · simp only [append, Fin.addCases_right, blockPerm_right, Fin.val_natAdd, Nat.cast_add, huv]
      ring
  · have hzero : (0 : Fin ((a + 1) + (b + 1))) = (0 : Fin (a + 1)).castAdd (b + 1) := Fin.ext rfl
    have hr' : r 0 = 0 := by
      convert hr using 1 <;> congr 1
    rw [hzero, blockPerm_left, hr']
  · have hlast : Fin.last ((a + 1) + b) = (Fin.last b).natAdd (a + 1) := Fin.ext rfl
    rw [hlast, blockPerm_right]
    have hv' : v (Fin.last b) = Fin.last b := by
      convert hv using 1 <;> congr 1
    rw [hv']

end XRay
