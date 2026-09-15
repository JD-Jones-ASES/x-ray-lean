import XRay.Basic

namespace XRay
open Finset

/-- Lower each row coordinate by one, clipping at zero. -/
def clippedRow {m : ℕ} (i : Fin (m + 1)) : Fin (m + 1) :=
  ⟨i.val - 1, by omega⟩

/-- Raise each column coordinate by one, clipping at the final coordinate. -/
def clippedCol {m : ℕ} (j : Fin (m + 1)) : Fin (m + 1) :=
  ⟨min (j.val + 1) m, by omega⟩

/-- A supplied permutation remains degree two after the opposite clipped shifts. -/
theorem clipped_degreeTwo {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    DegreeTwo clippedRow (clippedCol ∘ p) := by
  intro x
  unfold incidence
  rw [sum_add_distrib]
  have hu : (∑ i : Fin (m + 1), if clippedRow i = x then 1 else 0) =
      (if x.val < m then 1 else 0) + (if x = 0 then 1 else 0) := by
    rw [Fin.sum_univ_succ]
    have hz : clippedRow (0 : Fin (m + 1)) = 0 := Fin.ext rfl
    rw [hz]
    have hm : (∑ i : Fin m, if clippedRow i.succ = x then 1 else 0) =
        if x.val < m then 1 else 0 := by
      by_cases hx : x.val < m
      · have he (i : Fin m) : clippedRow i.succ = x ↔ i = ⟨x.val, hx⟩ := by
          simp only [clippedRow, Fin.ext_iff, Fin.val_succ, Nat.add_sub_cancel]
        simp [he, hx]
      · have he (i : Fin m) : clippedRow i.succ ≠ x := by
          intro he
          have hv := congrArg Fin.val he
          change i.val = x.val at hv
          omega
        simp [he, hx]
    rw [hm]
    simp [eq_comm, add_comm]
  have hv : (∑ i : Fin (m + 1), if clippedCol (p i) = x then 1 else 0) =
      (if 0 < x.val then 1 else 0) + (if x.val = m then 1 else 0) := by
    rw [Equiv.sum_comp p (fun j => if clippedCol j = x then (1 : ℕ) else 0), Fin.sum_univ_castSucc]
    have hz : clippedCol (Fin.last m) = Fin.last m := by apply Fin.ext; simp [clippedCol]
    rw [hz]
    have hm : (∑ i : Fin m, if clippedCol i.castSucc = x then 1 else 0) =
        if 0 < x.val then 1 else 0 := by
      by_cases hx : 0 < x.val
      · let j : Fin m := ⟨x.val - 1, by omega⟩
        have he (i : Fin m) : clippedCol i.castSucc = x ↔ i = j := by
          simp only [clippedCol, Fin.ext_iff, Fin.val_castSucc, j]
          have hi := i.isLt
          omega
        simp [he, hx]
      · have he (i : Fin m) : clippedCol i.castSucc ≠ x := by
          intro he
          have hv := congrArg Fin.val he
          change min (i.val + 1) m = x.val at hv
          have hi := i.isLt
          omega
        simp [he, hx]
    rw [hm]
    simp only [Fin.ext_iff, Fin.val_last]
    simp [eq_comm]
  change (∑ i, if clippedRow i = x then 1 else 0) +
    (∑ i, if clippedCol (p i) = x then 1 else 0) = 2
  rw [hu, hv]
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> omega

/-- First-row labels increase by one and last-column labels decrease by one.
If these describe the same cell, the two changes cancel. -/
def compressed {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) : Profile (m + 1) :=
  fun i => (i.val : ℤ) + (p i).val + 1 + (if i.val = 0 then 1 else 0) -
    (if (p i).val = m then 1 else 0)

 theorem compressed_realizable {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    Realizable (compressed p) := by
  apply realizable_of_degreeTwo (clipped_degreeTwo p)
  intro i
  simp only [compressed, clippedRow, clippedCol, Function.comp_apply]
  have hi := i.isLt
  have hp := (p i).isLt
  split_ifs <;> omega

/-- Opposite clipped shifts also work when cells are indexed by label rank. -/
theorem clipped_assignments {m : ℕ} (r c : Equiv.Perm (Fin (m + 1))) :
    DegreeTwo (clippedRow ∘ r) (clippedCol ∘ c) := by
  have h := (clipped_degreeTwo (r.symm.trans c)).reindex r
  simpa only [Function.comp_def, Equiv.trans_apply, Equiv.symm_apply_apply] using h

/-- Move the two extreme ranked labels inward by one. -/
def compressExtremes {m : ℕ} (L : Profile (m + 1)) : Profile (m + 1) :=
  fun i => L i + (if i.val = 0 then 1 else 0) - (if i.val = m then 1 else 0)

/-- Compression with a first-row minimum cell and a last-column maximum cell. -/
theorem compress_with_anchors {m : ℕ} {L : Profile (m + 1)}
    (r c : Equiv.Perm (Fin (m + 1)))
    (hrc : ∀ i, L i = (r i).val + (c i).val + (1 : ℤ))
    (hr : r 0 = 0) (hc : c (Fin.last m) = Fin.last m) :
    Realizable (compressExtremes L) := by
  apply realizable_of_degreeTwo (clipped_assignments r c)
  intro i
  have hz : (r i).val = 0 ↔ i.val = 0 := by
    constructor
    · intro h
      have hi : r i = r 0 := (Fin.ext h).trans hr.symm
      exact congrArg Fin.val (r.injective hi)
    · intro h
      have hi : i = 0 := Fin.ext h
      simp [hi, hr]
  have he : (c i).val = m ↔ i.val = m := by
    constructor
    · intro h
      have hi : c i = c (Fin.last m) := (Fin.ext h).trans hc.symm
      exact congrArg Fin.val (c.injective hi)
    · intro h
      have hi : i = Fin.last m := Fin.ext h
      simp [hi, hc]
  have hir := (r i).isLt
  have hic := (c i).isLt
  simp only [compressExtremes, hrc i, clippedRow, clippedCol, Function.comp_apply]
  split_ifs <;> omega

end XRay
