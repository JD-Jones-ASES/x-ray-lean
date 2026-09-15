import XRay.Switching

namespace XRay
open Finset

/-- The partial injection `r ↦ p(r) - 3`, in one-based coordinates. -/
noncomputable def shifted {n : ℕ} (p : Equiv.Perm (Fin n)) (x : ℤ) : ℤ :=
  if hx : 0 ≤ x - 1 ∧ x - 1 < (n : ℤ) then
    ((p ⟨(x - 1).toNat, by omega⟩).val : ℤ) - 2 else 0

@[simp] theorem shifted_apply {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) :
    shifted p ((i.val : ℤ) + 1) = (p i).val - (2 : ℤ) := by
  have hi : (i.val : ℤ) < n := by exact_mod_cast i.isLt
  simp only [shifted, add_sub_cancel_right, Nat.cast_nonneg, true_and,
    hi, dite_true, Int.toNat_natCast, Fin.eta]

 theorem mem_board_indices {n : ℕ} {x : ℤ} (h : x ∈ board n) :
    ∃ i : Fin n, (i.val : ℤ) + 1 = x := by
  have hm : x ∈ (board n).val := h
  rw [board_eq_indices] at hm
  simpa only [Multiset.mem_map, mem_univ_val, true_and] using hm

 theorem shifted_injective {n : ℕ} (p : Equiv.Perm (Fin n)) :
    Set.InjOn (shifted p) (board n) := by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := mem_board_indices hx
  obtain ⟨j, rfl⟩ := mem_board_indices hy
  rw [shifted_apply, shifted_apply] at hxy
  have hp : p i = p j := by apply Fin.ext; omega
  rw [p.injective hp]

 theorem shifted_bounds {n : ℕ} (p : Equiv.Perm (Fin n)) {x : ℤ} (hx : x ∈ board n) :
    -2 ≤ shifted p x ∧ shifted p x ≤ (n : ℤ) - 3 := by
  obtain ⟨i, rfl⟩ := mem_board_indices hx
  rw [shifted_apply]
  have hi := (p i).isLt
  constructor <;> omega

 theorem shifted_source {n : ℕ} (p : Equiv.Perm (Fin n)) {s : ℤ}
    (hs : (n : ℤ) - 3 < s) : s ∉ (board n).image (shifted p) := by
  rintro h
  obtain ⟨x, hx, rfl⟩ := mem_image.mp h
  have hb := (shifted_bounds p hx).2
  omega

 theorem shifted_column_margin {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (board n).val.map (fun x => shifted p x + 3) = (board n).val := by
  rw [board_eq_indices, Multiset.map_map]
  have hf : (fun i : Fin n => shifted p ((i.val : ℤ) + 1) + 3) =
      (fun i => (p i).val + (1 : ℤ)) := by
    funext i
    rw [shifted_apply]
    ring
  change univ.val.map (fun i : Fin n => shifted p ((i.val : ℤ) + 1) + 3) = _
  rw [hf]
  change univ.val.map ((fun j : Fin n => (j.val : ℤ) + 1) ∘ p) = _
  rw [← Multiset.map_map]
  rw [Multiset.map_univ_val_equiv p]

/-- At least one of the two eligible high sources reaches an eligible low sink. -/
theorem eligible_shell_path {n : ℕ} (hn : 3 ≤ n) (p : Equiv.Perm (Fin n)) :
    ∃ s t : ℤ, (s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1) ∧
      (t = -1 ∨ t = 0) ∧ Nonempty (PathSupport (board n) (shifted p) s t) := by
  have hs₁ := shifted_source p (s := (n : ℤ) - 2) (by omega)
  have hs₂ := shifted_source p (s := (n : ℤ) - 1) (by omega)
  obtain ⟨t₁, ⟨P⟩⟩ := exists_pathSupport (board n) (shifted p)
    (shifted_injective p) ((n : ℤ) - 2) hs₁
  obtain ⟨t₂, ⟨Q⟩⟩ := exists_pathSupport (board n) (shifted p)
    (shifted_injective p) ((n : ℤ) - 1) hs₂
  have sink_bounds {s t : ℤ} (hs : s ∈ board n)
      (R : PathSupport (board n) (shifted p) s t) : -2 ≤ t ∧ t ≤ 0 := by
    have hm : t ∈ R.vertices.val.map (shifted p) + {s} := by
      rw [R.balance]; simp
    have hne : t ≠ s := by intro he; exact R.terminal (he ▸ hs)
    rcases Multiset.mem_add.mp hm with hm | hm
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hm
      have hb := shifted_bounds p (R.subset_domain hx)
      have ht := R.terminal
      simp only [board, mem_Icc, not_and] at ht
      constructor
      · exact hb.1
      · by_contra hh
        exact ht (by omega) (by omega)
    · exact (hne (by simpa using hm)).elim
  have hb₁ := sink_bounds (s := (n : ℤ) - 2) (by simp [board]; omega) P
  have hb₂ := sink_bounds (s := (n : ℤ) - 1) (by simp [board]; omega) Q
  have hne := P.terminal_ne Q (shifted_injective p) hs₁ hs₂ (by omega)
  by_cases ht : t₁ = -2
  · exact ⟨(n : ℤ) - 1, t₂, Or.inr rfl, by omega, ⟨Q⟩⟩
  · exact ⟨(n : ℤ) - 2, t₁, Or.inl rfl, by omega, ⟨P⟩⟩

end XRay
