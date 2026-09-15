import XRay.OneSided
import XRay.PromotionInjection
import XRay.CountStats

namespace XRay
open Finset

/-- The minimum-label undirected edge touches the first board vertex. -/
def HasMinEdge {n : ℕ} (L : Profile n) (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, i.val = 0 → (1, L i) ∈ matrixCells p ∨ (L i, 1) ∈ matrixCells p

abbrev MarkedFiber {n : ℕ} (L : Profile n) :=
  {p : Equiv.Perm (Fin n) // labels p = univ.val.map L ∧ HasMinEdge L p}

noncomputable def anchoredCount {n : ℕ} (L : Profile n) : ℕ := by
  classical
  exact Fintype.card (MarkedFiber L)

 theorem mem_matrixCells_transpose {n : ℕ} (p : Equiv.Perm (Fin n)) (z : ℤ × ℤ) :
    z ∈ matrixCells p.symm ↔ z.swap ∈ matrixCells p := by
  rw [matrixCells_transpose]
  constructor
  · rintro h
    obtain ⟨w, hw, he⟩ := Multiset.mem_map.mp h
    have he' : w = z.swap := by simpa only [Prod.swap_swap] using congrArg Prod.swap he
    exact he' ▸ hw
  · intro h
    exact Multiset.mem_map.mpr ⟨z.swap, h, Prod.swap_swap z⟩

 theorem first_cell_iff {m : ℕ} (p : Equiv.Perm (Fin (m + 1))) (z : ℤ) :
    (1, z) ∈ matrixCells p ↔ (p 0).val + (1 : ℤ) = z := by
  constructor
  · intro h
    obtain ⟨i, _, he⟩ := Multiset.mem_map.mp h
    have hi : i = 0 := by
      have hh := congrArg Prod.fst he
      apply Fin.ext
      change i.val = 0
      change (i.val : ℤ) + 1 = 1 at hh
      omega
    simpa only [hi] using congrArg Prod.snd he
  · intro h
    exact Multiset.mem_map.mpr ⟨0, by simp, by simp [h]⟩

 theorem HasMinEdge.of_first {m : ℕ} {L : Profile (m + 1)} {p : Equiv.Perm (Fin (m + 1))}
    (h : (1, L 0) ∈ matrixCells p ∨ (L 0, 1) ∈ matrixCells p) : HasMinEdge L p := by
  intro i hi
  have he : i = 0 := Fin.ext hi
  simpa only [he] using h

 theorem HasMinEdge.transpose {n : ℕ} {L : Profile n} {p : Equiv.Perm (Fin n)}
    (h : HasMinEdge L p) : HasMinEdge L p.symm := by
  intro i hi
  rcases h i hi with h | h
  · exact Or.inr ((mem_matrixCells_transpose p _).mpr h)
  · exact Or.inl ((mem_matrixCells_transpose p _).mpr h)

 theorem HasMinEdge.transposeBit {n : ℕ} {L : Profile n} {p : Equiv.Perm (Fin n)}
    (h : HasMinEdge L p) (b : Bool) : HasMinEdge L (XRay.transposeBit b p) := by
  cases b
  · exact h
  · exact h.transpose

 theorem HasMinEdge.normalize {m : ℕ} {L : Profile (m + 1)} {p : Equiv.Perm (Fin (m + 1))}
    (h : HasMinEdge L p) :
    ∃ b : Bool, ((XRay.transposeBit b p) 0).val + (1 : ℤ) = L 0 := by
  rcases h 0 rfl with h | h
  · exact ⟨false, (first_cell_iff p _).mp h⟩
  · exact ⟨true, (first_cell_iff p.symm _).mp ((mem_matrixCells_transpose p _).mpr h)⟩

 theorem anchoredCount_le_fiberCount {n : ℕ} (L : Profile n) : anchoredCount L ≤ fiberCount L := by
  classical
  let f : MarkedFiber L → {p : Equiv.Perm (Fin n) // labels p = univ.val.map L} :=
    fun p => ⟨p.val, p.property.1⟩
  apply Fintype.card_le_of_injective f
  intro p q h
  apply Subtype.ext
  exact congrArg (fun x : {p : Equiv.Perm (Fin n) // labels p = univ.val.map L} => x.val) h

 theorem one_le_anchoredCount {n : ℕ} {L : Profile n} (h : MinAnchored L) :
    1 ≤ anchoredCount L := by
  classical
  have hex : Nonempty (MarkedFiber L) := by
    cases n with
    | zero => exact ⟨⟨Equiv.refl _, by simp [labels],
        fun i => Fin.elim0 i⟩⟩
    | succ m =>
      obtain ⟨p, hp, hp0⟩ := h.first_row
      exact ⟨⟨p, hp, HasMinEdge.of_first (Or.inl ((first_cell_iff p _).mpr hp0))⟩⟩
  exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr hex)

 theorem labels_blockPerm {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    labels (blockPerm p q) = labels p + (labels q).map (fun z => z + 2 * (m : ℤ)) := by
  unfold labels
  have he : (fun i : Fin (m + n) => (i.val : ℤ) + (blockPerm p q i).val + 1) =
      Fin.addCases (fun i : Fin m => (i.val : ℤ) + (p i).val + 1)
        (fun i : Fin n => (i.val : ℤ) + (q i).val + 1 + 2 * (m : ℤ)) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · simp only [blockPerm_right, Fin.val_natAdd, Nat.cast_add, Fin.addCases_right]
      ring
  rw [he, map_addCases, Multiset.map_map]
  rfl

 theorem blockPerm_pair_injective {m n : ℕ} :
    Function.Injective (fun z : Equiv.Perm (Fin m) × Equiv.Perm (Fin n) => blockPerm z.1 z.2) := by
  intro a b he
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have hh := congrArg (fun p : Equiv.Perm (Fin (m + n)) => p (i.castAdd n)) he
    simpa only [blockPerm_left, Fin.castAdd_inj] using hh
  · apply Equiv.ext
    intro i
    have hh := congrArg (fun p : Equiv.Perm (Fin (m + n)) => p (i.natAdd m)) he
    simpa only [blockPerm_right, Fin.natAdd_inj] using hh

 theorem matrixCells_block_left {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n))
    {z : ℤ × ℤ} (hz : z ∈ matrixCells p) : z ∈ matrixCells (blockPerm p q) := by
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hz
  exact Multiset.mem_map.mpr ⟨i.castAdd n, by simp, by simp⟩

 theorem HasMinEdge.block {m n : ℕ} {A : Profile m} {B : Profile n}
    {p : Equiv.Perm (Fin m)} {q : Equiv.Perm (Fin n)}
    (hm : 0 < m) (h : HasMinEdge A p) : HasMinEdge (append A B) (blockPerm p q) := by
  intro i hi
  let j : Fin m := ⟨0, hm⟩
  have he : i = j.castAdd n := Fin.ext hi
  rw [he]
  simp only [append, Fin.addCases_left]
  rcases h j rfl with h | h
  · exact Or.inl (matrixCells_block_left p q h)
  · exact Or.inr (matrixCells_block_left p q h)

 theorem anchoredCount_append {m n : ℕ} (hm : 0 < m) (A : Profile m) (B : Profile n) :
    anchoredCount A * anchoredCount B ≤ anchoredCount (append A B) := by
  classical
  let f : MarkedFiber A × MarkedFiber B → MarkedFiber (append A B) := fun z =>
    ⟨blockPerm z.1.val z.2.val, by
      rw [labels_blockPerm, z.1.property.1, z.2.property.1]
      change _ = univ.val.map (Fin.addCases A (fun i => B i + 2 * (m : ℤ)))
      rw [map_addCases, Multiset.map_map]
      rfl,
      z.1.property.2.block hm⟩
  have hf : Function.Injective f := by
    intro a b he
    have hh : (a.1.val, a.2.val) = (b.1.val, b.2.val) :=
      blockPerm_pair_injective (m := m) (n := n) (congrArg Subtype.val he)
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  simpa only [anchoredCount, Fintype.card_prod] using Fintype.card_le_of_injective f hf

end XRay
