import XRay.Basic

namespace XRay
open Finset

/-- Promote the first-row label by one, and add the final high label.
The first `m` slots retain the other source cells. -/
def promoted {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) : Profile (m + 2) :=
  Fin.addCases
    (fun i : Fin m => ((i.val : ℤ) + 1) + (p i.succ).val + 1)
    ![(p 0).val + (2 : ℤ), 2 * (m + 1 : ℤ)]

private def lo {m : ℕ} (_p : Equiv.Perm (Fin (m + 1))) : Fin (m + 2) → Fin (m + 2) :=
  Fin.addCases (fun i : Fin m => ⟨i.val, by omega⟩) ![0, ⟨m, by omega⟩]

private def hi {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) : Fin (m + 2) → Fin (m + 2) :=
  Fin.addCases (fun i : Fin m => (p i.succ).succ) ![(p 0).succ, Fin.last (m + 1)]

/-- The promotion graph has two incidences at every target vertex. -/
theorem promotion_degreeTwo {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    DegreeTwo (lo p) (hi p) := by
  intro x
  unfold incidence
  rw [Finset.sum_add_distrib]
  have hu : ∑ e, (if lo p e = x then 1 else 0) =
      (if x.val < m then 1 else 0) + (if x = 0 then 1 else 0) +
        (if x.val = m then 1 else 0) := by
    rw [Fin.sum_univ_add]
    simp +instances only [lo, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hc : ∑ i : Fin m, (if (⟨i.val, by omega⟩ : Fin (m + 2)) = x then 1 else 0) =
        if x.val < m then 1 else 0 := by
      by_cases hxm : x.val < m
      · have he (i : Fin m) : ((⟨i.val, by omega⟩ : Fin (m + 2)) = x) ↔ i = ⟨x.val, hxm⟩ := by
          simp only [Fin.ext_iff]
        simp [he, hxm]
      · have he (i : Fin m) : (⟨i.val, by omega⟩ : Fin (m + 2)) ≠ x := by
          intro h; have hv := congrArg Fin.val h; change i.val = x.val at hv; omega
        simp [he, hxm]
    rw [hc]
    simp only [Fin.ext_iff, Fin.val_zero]
    simp [eq_comm, Nat.add_assoc]
  have hv : ∑ e, (if hi p e = x then 1 else 0) =
      (if 0 < x.val then 1 else 0) + (if x.val = m + 1 then 1 else 0) := by
    rw [Fin.sum_univ_add]
    simp +instances only [hi, Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    have hs : (∑ i : Fin m, if (p i.succ).succ = x then 1 else 0) +
        (if (p 0).succ = x then 1 else 0) = if 0 < x.val then 1 else 0 := by
      rw [add_comm, ← Fin.sum_univ_succ (fun i : Fin (m + 1) => if (p i).succ = x then (1 : ℕ) else 0),
        Equiv.sum_comp p (fun y => if y.succ = x then (1 : ℕ) else 0)]
      by_cases hx : 0 < x.val
      · let j : Fin (m + 1) := ⟨x.val - 1, by omega⟩
        have he (i : Fin (m + 1)) : i.succ = x ↔ i = j := by
          simp only [Fin.ext_iff, Fin.val_succ, j]
          omega
        simp [he, hx]
      · have he (i : Fin (m + 1)) : i.succ ≠ x := by
          intro h; have hv := congrArg Fin.val h; simp only [Fin.val_succ] at hv; omega
        simp [he, hx]
    change (∑ i : Fin m, if (p i.succ).succ = x then 1 else 0) +
      ((if (p 0).succ = x then 1 else 0) + (if Fin.last (m + 1) = x then 1 else 0)) = _
    rw [← add_assoc, hs]
    simp only [Fin.ext_iff, Fin.val_last]
    simp [eq_comm]
  rw [hu, hv]
  simp only [Fin.ext_iff, Fin.val_zero]
  split_ifs <;> omega

/-- Ordinary promotion works for every supplied permutation, even when its
labels repeat. The two-output counting statement requires a separate inverse. -/
theorem promoted_realizable {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    Realizable (promoted p) := by
  apply realizable_of_degreeTwo (promotion_degreeTwo p)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [promoted, lo, hi, Fin.val_succ]
    ring
  · fin_cases j <;> simp [promoted, lo, hi, Fin.val_succ] <;> ring

end XRay
