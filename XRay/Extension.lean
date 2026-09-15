import XRay.ShellPath

namespace XRay
open Finset

/-- The source permutation's labels, indexed by its rows. -/
def cellProfile {n : ℕ} (p : Equiv.Perm (Fin n)) : Profile n :=
  fun i => (i.val : ℤ) + (p i).val + 1

/-- The ordinary extension for a supplied source of order at least three. -/
theorem extend_cellProfile_of_three_le {n : ℕ} (hn : 3 ≤ n)
    (p : Equiv.Perm (Fin n)) : Realizable (extend (cellProfile p)) := by
  classical
  obtain ⟨s, t, hs, ht, ⟨P⟩⟩ := eligible_shell_path hn p
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
  apply realizable_of_integer_margins a b ha hb
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [a, b, extend, Fin.addCases_left, cellProfile]
    rw [switched_label, shifted_apply]
    ring
  · fin_cases j <;> simp [a, b, extend] <;> ring

private theorem extend_order_one (p : Equiv.Perm (Fin 1)) :
    Realizable (extend (cellProfile p)) := by
  have hp : cellProfile p = ![1] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp [cellProfile, hi]
  rw [hp]
  apply realizable_of_integer_margins ![1, 2, 3] ![3, 2, 1]
  · rw [board_eq_indices]; decide
  · rw [board_eq_indices]; decide
  · decide

private theorem extend_order_two (p : Equiv.Perm (Fin 2)) :
    Realizable (extend (cellProfile p)) := by
  have hn : p 1 ≠ p 0 := fun h => (by decide : (1 : Fin 2) ≠ 0) (p.injective h)
  have h0 := (p 0).isLt
  have h1 := (p 1).isLt
  by_cases h : (p 0).val = 0
  · have hp0 : p 0 = 0 := Fin.ext h
    have hp1 : p 1 = 1 := by
      apply Fin.ext
      have hne : (p 1).val ≠ 0 := fun he => hn ((Fin.ext he).trans hp0.symm)
      omega
    have hp : cellProfile p = ![1, 3] := by
      funext i
      fin_cases i <;> simp [cellProfile, hp0, hp1]
    rw [hp]
    apply realizable_of_integer_margins ![1, 2, 3, 4] ![3, 4, 1, 2]
    · rw [board_eq_indices]; decide
    · rw [board_eq_indices]; decide
    · decide
  · have hp0 : p 0 = 1 := by apply Fin.ext; omega
    have hp1 : p 1 = 0 := by
      apply Fin.ext
      have hne : (p 1).val ≠ 1 := fun he => hn ((Fin.ext he).trans hp0.symm)
      omega
    have hp : cellProfile p = ![2, 2] := by
      funext i
      fin_cases i <;> simp [cellProfile, hp0, hp1]
    rw [hp]
    apply realizable_of_integer_margins ![3, 4, 1, 2] ![2, 1, 3, 4]
    · rw [board_eq_indices]; decide
    · rw [board_eq_indices]; decide
    · decide

 theorem extend_cellProfile {n : ℕ} (hn : 1 ≤ n) (p : Equiv.Perm (Fin n)) :
    Realizable (extend (cellProfile p)) := by
  by_cases h3 : 3 ≤ n
  · exact extend_cellProfile_of_three_le h3 p
  · interval_cases n
    · exact extend_order_one p
    · exact extend_order_two p

 theorem extend_multiset {n : ℕ} (L : Profile n) :
    univ.val.map (extend L) = (univ.val.map L).map (fun x => x + 2) +
      {3} + {2 * (n : ℤ) + 1} := by
  unfold extend
  rw [map_addCases, Multiset.map_map]
  simp only [Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, ← Multiset.cons_coe,
    Multiset.coe_nil, ← Multiset.singleton_add, add_zero, Function.comp_def]
  ac_rfl

/-- The ordinary Q extension holds for every supplied realization. There is
no binary, endpoint-anchor, or slack hypothesis. -/
theorem ordinary_extension {n : ℕ} (hn : 1 ≤ n) {L : Profile n}
    (h : Realizable L) : Realizable (extend L) := by
  obtain ⟨p, hp⟩ := h.matrix
  apply (extend_cellProfile hn p).of_multiset
  rw [extend_multiset, extend_multiset]
  change _ = (labels p).map (fun x => x + 2) + {3} + {2 * (n : ℤ) + 1}
  rw [hp]

end XRay
