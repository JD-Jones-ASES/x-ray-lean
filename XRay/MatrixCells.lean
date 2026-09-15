import XRay.IntegerCells

namespace XRay
open Finset

/-- Literal one-based cells of a permutation. -/
def matrixCells {n : ℕ} (p : Equiv.Perm (Fin n)) : Multiset (ℤ × ℤ) :=
  univ.val.map (fun i => ((i.val : ℤ) + 1, (p i).val + (1 : ℤ)))

 theorem matrixCells_labels {n : ℕ} (p : Equiv.Perm (Fin n)) :
    (matrixCells p).map (fun z => z.1 + z.2 - 1) = labels p := by
  unfold matrixCells labels
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  dsimp
  ring

 theorem matrixCells_injective {n : ℕ} :
    Function.Injective (matrixCells (n := n)) := by
  intro p q heq
  apply Equiv.ext
  intro i
  have hm : ((i.val : ℤ) + 1, (p i).val + (1 : ℤ)) ∈ matrixCells q := by
    rw [← heq]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨j, _, he⟩ := Multiset.mem_map.mp hm
  have hij : j = i := by
    have hh := congrArg Prod.fst he
    apply Fin.ext
    change (j.val : ℤ) + 1 = (i.val : ℤ) + 1 at hh
    omega
  subst j
  have hh := congrArg Prod.snd he
  apply Fin.ext
  change (q i).val + (1 : ℤ) = (p i).val + (1 : ℤ) at hh
  omega

/-- Retain the literal cells when constructing a permutation from exact margins. -/
theorem matrix_of_integer_margins {n : ℕ} (a b : Fin n → ℤ)
    (ha : univ.val.map a = (board n).val)
    (hb : univ.val.map b = (board n).val) :
    ∃ p : Equiv.Perm (Fin n), matrixCells p = univ.val.map (fun i => (a i, b i)) := by
  rw [board_eq_indices] at ha hb
  obtain ⟨r, hr⟩ := equiv_of_map_univ_eq ha
  obtain ⟨c, hc⟩ := equiv_of_map_univ_eq hb
  refine ⟨r.symm.trans c, ?_⟩
  unfold matrixCells
  conv_lhs => rw [← Multiset.map_univ_val_equiv r, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simp only [Function.comp_def, Equiv.trans_apply, r.symm_apply_apply, hr, hc]

 theorem matrixCells_transpose {n : ℕ} (p : Equiv.Perm (Fin n)) :
    matrixCells p.symm = (matrixCells p).map Prod.swap := by
  unfold matrixCells
  conv_lhs => rw [← Multiset.map_univ_val_equiv p, Multiset.map_map]
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simp only [Function.comp_def, p.symm_apply_apply, Prod.swap_prod_mk]

/-- Exact margins characterize finite cell multisets of permutation matrices. -/
theorem matrix_of_multiset_margins {n : ℕ} (M : Multiset (ℤ × ℤ))
    (hr : M.map Prod.fst = (board n).val)
    (hc : M.map Prod.snd = (board n).val) :
    ∃ p : Equiv.Perm (Fin n), matrixCells p = M := by
  obtain ⟨l, rfl⟩ := Quotient.exists_rep M
  have hn : l.length = n := by
    simpa [board_eq_indices] using congrArg Multiset.card hr
  subst n
  have he : univ.val.map l.get = (l : Multiset (ℤ × ℤ)) := by
    rw [Fin.univ_val_map, List.ofFn_get]
  have hr' : univ.val.map (fun i => (l.get i).1) = (board l.length).val := by
    simpa only [Multiset.map_map, Function.comp_def] using
      (congrArg (Multiset.map Prod.fst) he).trans hr
  have hc' : univ.val.map (fun i => (l.get i).2) = (board l.length).val := by
    simpa only [Multiset.map_map, Function.comp_def] using
      (congrArg (Multiset.map Prod.snd) he).trans hc
  obtain ⟨p, hp⟩ := matrix_of_integer_margins _ _ hr' hc'
  exact ⟨p, hp.trans he⟩

end XRay
