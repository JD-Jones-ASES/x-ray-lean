import XRay.MatrixCells
import XRay.Extension
import XRay.SwitchInverse

namespace XRay
open Finset

/-- Literal cells of the ordinary shell construction. -/
noncomputable def shellCells {n : ℕ} (p : Equiv.Perm (Fin n))
    (P : Finset ℤ) (s t : ℤ) : Multiset (ℤ × ℤ) :=
  (board n).val.map (fun x => (switchedRow P (shifted p) x, switchedCol P (shifted p) x)) +
    {(1 - t, t + 3)} + {(s + 2, 2 * (n : ℤ) - s)}

/-- Every eligible support gives an actual matrix with precisely these cells. -/
theorem shellCells_matrix {n : ℕ} (p : Equiv.Perm (Fin n)) {s t : ℤ}
    (hs : s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1) (ht : t = -1 ∨ t = 0)
    (P : PathSupport (board n) (shifted p) s t) :
    ∃ q : Equiv.Perm (Fin (n + 2)), matrixCells q = shellCells p P.vertices s t := by
  classical
  let a : Fin (n + 2) → ℤ := Fin.addCases
    (fun i : Fin n => switchedRow P.vertices (shifted p) ((i.val : ℤ) + 1))
    ![1 - t, s + 2]
  let b : Fin (n + 2) → ℤ := Fin.addCases
    (fun i : Fin n => switchedCol P.vertices (shifted p) ((i.val : ℤ) + 1))
    ![t + 3, 2 * (n : ℤ) - s]
  have ha : univ.val.map a = (board (n + 2)).val := by
    dsimp only [a]
    rw [map_addCases]
    have hm : univ.val.map (fun i : Fin n => switchedRow P.vertices (shifted p)
        ((i.val : ℤ) + 1)) = (board n).val.map (switchedRow P.vertices (shifted p)) := by
      rw [board_eq_indices, Multiset.map_map]
      rfl
    rw [hm]
    simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ← Multiset.cons_coe,
      Multiset.coe_nil, ← Multiset.singleton_add, add_zero]
    calc
      _ = ((board n).val.map (switchedRow P.vertices (shifted p)) + {s + 2}) + {1 - t} := by ac_rfl
      _ = (board n).val.map (fun x => x + 2) + {t + 2} + {1 - t} := by rw [P.row_margin]
      _ = (board n).val.map (fun x => x + 2) + {1} + {2} := by
        rcases ht with rfl | rfl <;> norm_num; ac_rfl
      _ = _ := board_front_two n
  have hb : univ.val.map b = (board (n + 2)).val := by
    dsimp only [b]
    rw [map_addCases]
    have hm : univ.val.map (fun i : Fin n => switchedCol P.vertices (shifted p)
        ((i.val : ℤ) + 1)) = (board n).val.map (switchedCol P.vertices (shifted p)) := by
      rw [board_eq_indices, Multiset.map_map]
      rfl
    rw [hm]
    simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ← Multiset.cons_coe,
      Multiset.coe_nil, ← Multiset.singleton_add, add_zero]
    calc
      _ = ((board n).val.map (switchedCol P.vertices (shifted p)) + {t + 3}) +
          {2 * (n : ℤ) - s} := by ac_rfl
      _ = (board n).val + {s + 3} + {2 * (n : ℤ) - s} := by
        rw [P.col_margin, shifted_column_margin]
      _ = (board n).val + {(n : ℤ) + 1} + {(n : ℤ) + 2} := by
        rcases hs with rfl | rfl <;> ring_nf; ac_rfl
      _ = _ := board_back_two n
  obtain ⟨q, hq⟩ := matrix_of_integer_margins a b ha hb
  refine ⟨q, hq.trans ?_⟩
  have he : (fun i => (a i, b i)) = Fin.addCases
      (fun i : Fin n => (switchedRow P.vertices (shifted p) ((i.val : ℤ) + 1),
        switchedCol P.vertices (shifted p) ((i.val : ℤ) + 1)))
      ![(1 - t, t + 3), (s + 2, 2 * (n : ℤ) - s)] := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [a, b]
    · fin_cases j <;> simp [a, b]
  rw [he, map_addCases]
  simp only [shellCells, board_eq_indices, Multiset.map_map]
  simp only [Function.comp_def, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, ← Multiset.cons_coe, Multiset.coe_nil,
    ← Multiset.singleton_add, add_zero]
  ac_rfl

 theorem shellCells_labels {n : ℕ} (p : Equiv.Perm (Fin n)) (P : Finset ℤ) (s t : ℤ) :
    (shellCells p P s t).map (fun z => z.1 + z.2 - 1) =
      (labels p).map (fun z => z + 2) + {3} + {2 * (n : ℤ) + 1} := by
  simp only [shellCells, Multiset.map_add, Multiset.map_singleton, Multiset.map_map]
  have hlow : 1 - t + (t + 3) - 1 = (3 : ℤ) := by ring
  have hhigh : s + 2 + (2 * (n : ℤ) - s) - 1 = 2 * (n : ℤ) + 1 := by ring
  rw [hlow, hhigh]
  congr 2
  rw [board_eq_indices, Multiset.map_map]
  unfold labels
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  dsimp
  rw [switched_label, shifted_apply]
  ring

/-- At least one of the two eligible high sources reaches an eligible low sink. -/
theorem eligible_rooted_shell_path_of_three_le {n : ℕ} (hn : 3 ≤ n) (p : Equiv.Perm (Fin n)) :
    ∃ s t : ℤ, (s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1) ∧
      (t = -1 ∨ t = 0) ∧ Nonempty (RootedPath (board n) (shifted p) s t) := by
  have hs₁ := shifted_source p (s := (n : ℤ) - 2) (by omega)
  have hs₂ := shifted_source p (s := (n : ℤ) - 1) (by omega)
  obtain ⟨t₁, ⟨P⟩⟩ := exists_rootedPath (board n) (shifted p)
    (shifted_injective p) ((n : ℤ) - 2) hs₁
  obtain ⟨t₂, ⟨Q⟩⟩ := exists_rootedPath (board n) (shifted p)
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
  have hb₁ := sink_bounds (s := (n : ℤ) - 2) (by simp [board]; omega) P.toPathSupport
  have hb₂ := sink_bounds (s := (n : ℤ) - 1) (by simp [board]; omega) Q.toPathSupport
  have hne := P.toPathSupport.terminal_ne Q.toPathSupport (shifted_injective p) hs₁ hs₂ (by omega)
  by_cases ht : t₁ = -2
  · exact ⟨(n : ℤ) - 1, t₂, Or.inr rfl, by omega, ⟨Q⟩⟩
  · exact ⟨(n : ℤ) - 2, t₁, Or.inl rfl, by omega, ⟨P⟩⟩

 theorem eligible_rooted_shell_path {n : ℕ} (hn : 1 ≤ n) (p : Equiv.Perm (Fin n)) :
    ∃ s t : ℤ, (s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1) ∧
      (t = -1 ∨ t = 0) ∧ Nonempty (RootedPath (board n) (shifted p) s t) := by
  by_cases h3 : 3 ≤ n
  · exact eligible_rooted_shell_path_of_three_le h3 p
  · interval_cases n
    · refine ⟨-1, -1, Or.inl (by norm_num), Or.inl rfl, ⟨?_, ?_⟩⟩
      · exact ⟨∅, empty_subset _, by simp [board], by simp⟩
      · intro x hx; simp at hx
    · refine ⟨0, 0, Or.inl (by norm_num), Or.inr rfl, ⟨?_, ?_⟩⟩
      · exact ⟨∅, empty_subset _, by simp [board], by simp⟩
      · intro x hx; simp at hx

end XRay
