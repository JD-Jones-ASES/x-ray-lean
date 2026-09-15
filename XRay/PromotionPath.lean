import XRay.ShellMatrix
import XRay.SwitchMargins

namespace XRay
open Finset

/-- Core of promotion: delete the first source row, then translate by (-1,+1). -/
noncomputable def promotionCore {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) (x : ℤ) : ℤ :=
  if hx : 0 ≤ x ∧ x < (m + 1 : ℕ) then
    (p ⟨x.toNat, by omega⟩).val + (2 : ℤ) else 0

@[simp] theorem promotionCore_apply {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) (i : Fin m) :
    promotionCore p ((i.val : ℤ) + 1) = (p i.succ).val + (2 : ℤ) := by
  have hx : 0 ≤ (i.val : ℤ) + 1 ∧ (i.val : ℤ) + 1 < (m + 1 : ℕ) := by
    push_cast
    constructor <;> omega
  simp only [promotionCore, dif_pos hx]
  congr 2

 theorem promotionCore_injective {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    Set.InjOn (promotionCore p) (board m) := by
  intro x hx y hy hxy
  obtain ⟨i, rfl⟩ := mem_board_indices hx
  obtain ⟨j, rfl⟩ := mem_board_indices hy
  rw [promotionCore_apply, promotionCore_apply] at hxy
  have hh : p i.succ = p j.succ := by apply Fin.ext; omega
  have hij := Fin.succ_injective _ (p.injective hh)
  rw [hij]

 theorem promotionCore_bounds {m : ℕ} (p : Equiv.Perm (Fin (m + 1)))
    {x : ℤ} (hx : x ∈ board m) :
    2 ≤ promotionCore p x ∧ promotionCore p x ≤ (m : ℤ) + 2 ∧
      promotionCore p x ≠ (p 0).val + (2 : ℤ) := by
  obtain ⟨i, rfl⟩ := mem_board_indices hx
  rw [promotionCore_apply]
  have hi := (p i.succ).isLt
  refine ⟨by omega, by omega, ?_⟩
  intro hh
  have he : p i.succ = p 0 := by apply Fin.ext; omega
  have he' := p.injective he
  exact Fin.succ_ne_zero i he'

 theorem promotionCore_source {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    (1 : ℤ) ∉ (board m).image (promotionCore p) := by
  rintro h
  obtain ⟨x, hx, he⟩ := mem_image.mp h
  have hh := (promotionCore_bounds p hx).1
  omega

 theorem promotionCore_column_margin {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) :
    (board m).val.map (promotionCore p) + {(p 0).val + (2 : ℤ)} =
      (board (m + 1)).val.map (fun x => x + 1) := by
  have hall : univ.val.map (fun i : Fin (m + 1) => (p i).val + (2 : ℤ)) =
      univ.val.map (fun i : Fin (m + 1) => (i.val : ℤ) + 2) := by
    change univ.val.map ((fun i : Fin (m + 1) => (i.val : ℤ) + 2) ∘ p) = _
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv p]
  have hsplit : univ.val.map (fun i : Fin (m + 1) => (p i).val + (2 : ℤ)) =
      {(p 0).val + (2 : ℤ)} + univ.val.map (fun i : Fin m => (p i.succ).val + (2 : ℤ)) := by
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [← Multiset.cons_coe, ← Multiset.singleton_add, Fin.univ_val_map]
  rw [board_eq_indices, board_eq_indices, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, promotionCore_apply]
  rw [add_comm, ← hsplit, hall]
  congr 1

 theorem board_front_one (n : ℕ) :
    (board n).val.map (fun x => x + 1) + {1} = (board (n + 1)).val := by
  rw [board_eq_indices, board_eq_indices, Multiset.map_map]
  simp only [Function.comp_def, Fin.univ_val_map, List.ofFn_succ, Fin.val_succ,
    Fin.val_zero, Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_add,
    ← Multiset.cons_coe, ← Multiset.singleton_add]
  ac_rfl

 theorem promotion_rooted_path {m : ℕ} (hm : 1 ≤ m) (p : Equiv.Perm (Fin (m + 1))) :
    ∃ t : ℤ, (t = (m : ℤ) + 1 ∨ t = (m : ℤ) + 2) ∧
      Nonempty (RootedPath (board m) (promotionCore p) 1 t) := by
  obtain ⟨t, ⟨P⟩⟩ := exists_rootedPath (board m) (promotionCore p)
    (promotionCore_injective p) 1 (promotionCore_source p)
  have ht : t ≠ 1 := by
    intro he
    exact P.terminal (he ▸ (show (1 : ℤ) ∈ board m by simp [board]; omega))
  have hm : t ∈ P.vertices.val.map (promotionCore p) + {1} := by rw [P.balance]; simp
  rcases Multiset.mem_add.mp hm with hm | hm
  · obtain ⟨x, hx, he⟩ := Multiset.mem_map.mp hm
    have hb := promotionCore_bounds p (P.subset_domain hx)
    have hout := P.terminal
    simp only [board, mem_Icc, not_and] at hout
    have htlo : 1 ≤ t := by omega
    have htgt := hout htlo
    exact ⟨t, by omega, ⟨P⟩⟩
  · exact (ht (by simpa using hm)).elim

end XRay
