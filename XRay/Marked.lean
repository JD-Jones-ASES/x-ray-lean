import XRay.Blocks

namespace XRay

/-- A realization retaining an endpoint at the first board vertex for the
first-ranked label. Empty profiles satisfy the condition vacuously. -/
def MinAnchored {n : ℕ} (L : Profile n) : Prop :=
  ∃ r c : Equiv.Perm (Fin n),
    (∀ i, L i = (r i).val + (c i).val + (1 : ℤ)) ∧
    ∀ i, i.val = 0 → (r i).val = 0 ∨ (c i).val = 0

 theorem MinAnchored.realizable {n : ℕ} {L : Profile n} (h : MinAnchored L) :
    Realizable L := by
  obtain ⟨r, c, hrc, _⟩ := h
  exact ⟨r, c, hrc⟩

 theorem MinAnchored.first_row {m : ℕ} {L : Profile (m + 1)} (h : MinAnchored L) :
    ∃ p : Equiv.Perm (Fin (m + 1)), labels p = Finset.univ.val.map L ∧
      (p 0).val + (1 : ℤ) = L 0 := by
  obtain ⟨r, c, hrc, hzero⟩ := h
  apply first_row_of_zero_endpoint r c hrc
  rcases hzero 0 rfl with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

 theorem MinAnchored.append {m n : ℕ} {A : Profile m} {B : Profile n}
    (hm : 0 < m) (hA : MinAnchored A) (hB : Realizable B) :
    MinAnchored (XRay.append A B) := by
  obtain ⟨r, c, hrc, hz⟩ := hA
  obtain ⟨u, v, huv⟩ := hB
  refine ⟨blockPerm r u, blockPerm c v, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [XRay.append, Fin.addCases_left, blockPerm_left, Fin.val_castAdd, hrc]
    · simp only [XRay.append, Fin.addCases_right, blockPerm_right, Fin.val_natAdd,
        Nat.cast_add, huv]
      ring
  · intro i hi
    let j : Fin m := ⟨0, hm⟩
    have he : i = j.castAdd n := Fin.ext hi
    subst i
    simpa only [blockPerm_left, Fin.val_castAdd] using hz j rfl

/-- Transport a specified zero endpoint through multiset relabeling. Binary
labels identify which source edge becomes the minimum-ranked target edge. -/
theorem minAnchored_of_marked_multiset {m : ℕ} {A B : Profile (m + 1)}
    (hB : Function.Injective B)
    (heq : Finset.univ.val.map B = Finset.univ.val.map A)
    (r c : Equiv.Perm (Fin (m + 1)))
    (hrc : ∀ i, A i = (r i).val + (c i).val + (1 : ℤ))
    (j : Fin (m + 1)) (hj : A j = B 0)
    (hz : (r j).val = 0 ∨ (c j).val = 0) : MinAnchored B := by
  obtain ⟨e, he⟩ := equiv_of_map_univ_eq heq
  have hej : e 0 = j := by
    have hh : B (e.symm j) = B 0 := by
      rw [← he, e.apply_symm_apply, hj]
    have hh' := hB hh
    simpa only [e.apply_symm_apply] using (congrArg e hh').symm
  refine ⟨e.trans r, e.trans c, fun i => ?_, ?_⟩
  · simpa only [Equiv.trans_apply, ← he] using hrc (e i)
  · intro i hi
    have hi0 : i = 0 := Fin.ext hi
    simpa only [hi0, Equiv.trans_apply, hej] using hz

end XRay
