import XRay.PromotionPath

namespace XRay
open Finset

/-- Orient the new low edge outwards and the new high edge towards the chosen
path terminal; all other cells come from the rooted switch. -/
noncomputable def promotionCells {m : ℕ} (p : Equiv.Perm (Fin (m + 1)))
    (P : Finset ℤ) (t : ℤ) : Multiset (ℤ × ℤ) :=
  (board m).val.map (switchPair P (promotionCore p)) +
    {(1, (p 0).val + (2 : ℤ))} + {(2 * (m : ℤ) + 3 - t, t)}

 theorem promotionCells_matrix {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) {t : ℤ}
    (ht : t = (m : ℤ) + 1 ∨ t = (m : ℤ) + 2)
    (P : PathSupport (board m) (promotionCore p) 1 t) :
    ∃ q : Equiv.Perm (Fin (m + 2)), matrixCells q = promotionCells p P.vertices t := by
  apply matrix_of_multiset_margins
  · simp only [promotionCells, Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
      Function.comp_def]
    rw [P.switch_fst_margin]
    calc
      _ = (board m).val + {(m : ℤ) + 1} + {(m : ℤ) + 2} := by
        rcases ht with rfl | rfl <;> ring_nf; ac_rfl
      _ = _ := board_back_two m
  · simp only [promotionCells, Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
      Function.comp_def]
    calc
      _ = ((board m).val.map (fun x => (switchPair P.vertices (promotionCore p) x).2) + {t}) +
          {(p 0).val + (2 : ℤ)} := by ac_rfl
      _ = ((board m).val.map (promotionCore p) + {(p 0).val + (2 : ℤ)}) + {1} := by
        rw [P.switch_snd_margin]; ac_rfl
      _ = _ := by rw [promotionCore_column_margin, board_front_one]

 theorem promotionCells_labels {m : ℕ} (p : Equiv.Perm (Fin (m + 1)))
    (P : Finset ℤ) (t : ℤ) :
    (promotionCells p P t).map (fun z => z.1 + z.2 - 1) + {(p 0).val + (1 : ℤ)} =
      labels p + {(p 0).val + (2 : ℤ)} + {2 * (m + 1 : ℤ)} := by
  have he (x : ℤ) : (switchPair P (promotionCore p) x).1 +
      (switchPair P (promotionCore p) x).2 - 1 = x + promotionCore p x - 1 := by
    simp only [switchPair]
    split_ifs <;> ring
  have hlow : 1 + ((p 0).val + (2 : ℤ)) - 1 = (p 0).val + (2 : ℤ) := by ring
  have hhigh : (2 * (m : ℤ) + 3 - t) + t - 1 = 2 * (m + 1 : ℤ) := by ring
  simp only [promotionCells, Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def, he, hlow, hhigh]
  rw [board_eq_indices, Multiset.map_map]
  simp only [Function.comp_def, promotionCore_apply]
  unfold labels
  have hsplit : univ.val.map (fun i : Fin (m + 1) => (i.val : ℤ) + (p i).val + 1) =
      {(p 0).val + (1 : ℤ)} +
        univ.val.map (fun i : Fin m => (i.val : ℤ) + 1 + (p i.succ).val + 1) := by
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_add, Fin.val_succ, Nat.cast_add, Nat.cast_one,
      ← Multiset.cons_coe, ← Multiset.singleton_add, Fin.univ_val_map]
  rw [hsplit]
  have hh : (fun i : Fin m => (i.val : ℤ) + 1 + ((p i.succ).val + 2) - 1) =
      (fun i : Fin m => (i.val : ℤ) + 1 + (p i.succ).val + 1) := by funext i; ring
  rw [hh]
  ac_rfl

 theorem promotionCells_no_reverse {m : ℕ} (hm : 1 ≤ m)
    (p : Equiv.Perm (Fin (m + 1))) (P : Finset ℤ) {t : ℤ}
    (ht : t = (m : ℤ) + 1 ∨ t = (m : ℤ) + 2) :
    ((p 0).val + (2 : ℤ), 1) ∉ promotionCells p P t := by
  intro h
  rcases Multiset.mem_add.mp h with h | h
  · rcases Multiset.mem_add.mp h with h | h
    · obtain ⟨x, hx, he⟩ := Multiset.mem_map.mp h
      have hb := promotionCore_bounds p hx
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      simp only [switchPair] at h₁ h₂
      split_ifs at h₁ h₂ <;> dsimp at h₁ h₂ <;> omega
    · have he : ((p 0).val + (2 : ℤ), 1) = (1, (p 0).val + (2 : ℤ)) := by simpa using h
      have hh := congrArg Prod.fst he
      dsimp at hh
      omega
  · have he : ((p 0).val + (2 : ℤ), 1) = (2 * (m : ℤ) + 3 - t, t) := by simpa using h
    have hh := congrArg Prod.snd he
    dsimp at hh
    rcases ht with ht | ht <;> omega

 theorem promotion_high_unique {m : ℕ} (hm : 1 ≤ m)
    (p : Equiv.Perm (Fin (m + 1))) (P : Finset ℤ) (t : ℤ) {z : ℤ × ℤ}
    (hz : z ∈ promotionCells p P t) (hl : z.1 + z.2 - 1 = 2 * (m + 1 : ℤ)) :
    z = (2 * (m : ℤ) + 3 - t, t) := by
  rcases Multiset.mem_add.mp hz with hz | hz
  · rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
      have hb := (promotionCore_bounds p hx).2.1
      have hx' : x ∈ board m := hx
      simp only [board, mem_Icc] at hx'
      simp only [switchPair] at hl
      split_ifs at hl <;> dsimp at hl <;> omega
    · have he : z = (1, (p 0).val + (2 : ℤ)) := by simpa using hz
      rw [he] at hl
      dsimp at hl
      have hp := (p 0).isLt
      omega
  · simpa using hz

 theorem promotionCells_injective {m : ℕ} (hm : 1 ≤ m)
    {p q : Equiv.Perm (Fin (m + 1))} (hzero : p 0 = q 0) {s t : ℤ}
    (P : RootedPath (board m) (promotionCore p) 1 s)
    (Q : RootedPath (board m) (promotionCore q) 1 t)
    (heq : promotionCells p P.vertices s = promotionCells q Q.vertices t) : p = q := by
  have hmem : (2 * (m : ℤ) + 3 - s, s) ∈ promotionCells q Q.vertices t := by
    rw [← heq]; simp [promotionCells]
  have hst : s = t := by
    exact congrArg Prod.snd (promotion_high_unique hm q Q.vertices t hmem (by dsimp; ring))
  subst t
  have he := add_right_cancel heq
  simp only [hzero] at he
  have he' : (board m).val.map (switchPair P.vertices (promotionCore p)) =
      (board m).val.map (switchPair Q.vertices (promotionCore q)) := add_right_cancel he
  have hi := (rooted_switch_injective P Q (promotionCore_injective p) (promotionCore_injective q)
    (promotionCore_source p) (promotionCore_source q) he').2
  apply Equiv.ext
  intro i
  refine Fin.cases hzero (fun j => ?_) i
  have hj : (j.val : ℤ) + 1 ∈ board m := by simp only [board, mem_Icc]; constructor <;> omega
  have hh := hi _ hj
  rw [promotionCore_apply, promotionCore_apply] at hh
  apply Fin.ext
  omega

end XRay
