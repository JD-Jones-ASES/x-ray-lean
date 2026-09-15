import XRay.Basic

namespace XRay
open Finset

/-- One-based coordinates of an `n` by `n` board. -/
noncomputable def board (n : ℕ) : Finset ℤ := Icc 1 (n : ℤ)

 theorem board_eq_indices (n : ℕ) :
    (board n).val = univ.val.map (fun i : Fin n => (i.val : ℤ) + 1) := by
  have hi : Function.Injective (fun i : Fin n => (i.val : ℤ) + 1) := by
    intro a b h
    apply Fin.ext
    change (a.val : ℤ) + 1 = (b.val : ℤ) + 1 at h
    omega
  have hs : board n = univ.image (fun i : Fin n => (i.val : ℤ) + 1) := by
    ext z
    simp only [board, mem_Icc, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨⟨(z - 1).toNat, by omega⟩, ?_⟩
      change ((z - 1).toNat : ℤ) + 1 = z
      omega
    · rintro ⟨i, rfl⟩
      constructor <;> omega
  rw [hs, image_val_of_injOn hi.injOn]

/-- Integer coordinates with the two exact board margins give a permutation
matrix. Range conditions follow from the margins and need not be assumed. -/
theorem realizable_of_integer_margins {n : ℕ} {L : Profile n}
    (a b : Fin n → ℤ) (ha : univ.val.map a = (board n).val)
    (hb : univ.val.map b = (board n).val)
    (hL : ∀ i, L i = a i + b i - 1) : Realizable L := by
  rw [board_eq_indices] at ha hb
  obtain ⟨r, hr⟩ := equiv_of_map_univ_eq ha
  obtain ⟨c, hc⟩ := equiv_of_map_univ_eq hb
  refine ⟨r, c, fun i => ?_⟩
  rw [hL i, ← hr i, ← hc i]
  ring

/-- Splitting a multiset map according to a subset of its finite domain. -/
theorem map_ite_of_subset {α β : Type*} [DecidableEq α]
    (D P : Finset α) (hP : P ⊆ D) (f g : α → β) :
    D.val.map (fun x => if x ∈ P then f x else g x) =
      P.val.map f + (SDiff.sdiff D P).val.map g := by
  have hd : Disjoint P (SDiff.sdiff D P) := disjoint_sdiff_self_right
  have hu : P ∪ (SDiff.sdiff D P) = D := union_sdiff_of_subset hP
  have hv : D.val = P.val + (SDiff.sdiff D P).val := by
    conv_lhs => rw [← hu, ← disjUnion_eq_union P (SDiff.sdiff D P) hd]
    rfl
  conv_lhs => rw [hv]
  rw [Multiset.map_add]
  congr 1
  · apply Multiset.map_congr rfl
    intro x hx
    exact if_pos hx
  · apply Multiset.map_congr rfl
    intro x hx
    exact if_neg (mem_sdiff.mp hx).2

/-- Decompose a two-block array without imposing an order on its values. -/
theorem map_addCases {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α) :
    univ.val.map (Fin.addCases f g) = univ.val.map f + univ.val.map g := by
  have hl (i : Fin m) : Fin.addCases f g (i.castLE (Nat.le_add_right m n)) = f i := by
    have he : i.castLE (Nat.le_add_right m n) = i.castAdd n := Fin.ext rfl
    rw [he, Fin.addCases_left]
  simp only [Fin.univ_val_map, List.ofFn_add, ← Multiset.coe_add, hl, Fin.addCases_right]

 theorem board_succ (n : ℕ) :
    (board (n + 1)).val = (board n).val + {(n : ℤ) + 1} := by
  simp only [board_eq_indices, Fin.univ_val_map, List.ofFn_succ_last,
    ← Multiset.coe_add, Multiset.coe_singleton, Fin.val_castSucc, Fin.val_last]

 theorem board_back_two (n : ℕ) :
    (board n).val + {(n : ℤ) + 1} + {(n : ℤ) + 2} = (board (n + 2)).val := by
  rw [← board_succ, show (n : ℤ) + 2 = ((n + 1 : ℕ) : ℤ) + 1 by push_cast; ring,
    ← board_succ]

 theorem board_front_two (n : ℕ) :
    (board n).val.map (fun x => x + 2) + {1} + {2} = (board (n + 2)).val := by
  rw [board_eq_indices, Multiset.map_map, board_eq_indices]
  simp only [Fin.univ_val_map, List.ofFn_succ, Fin.val_succ, Nat.cast_add,
    Nat.cast_one, Fin.val_zero, Nat.cast_zero, zero_add, ← Multiset.cons_coe]
  have he : (fun i : Fin n => (i.val : ℤ) + 1 + 2) =
      (fun i : Fin n => (i.val : ℤ) + 1 + 1 + 1) := by funext i; ring
  simp only [Function.comp_def, he, ← Multiset.singleton_add]
  norm_num only
  ac_rfl

end XRay
