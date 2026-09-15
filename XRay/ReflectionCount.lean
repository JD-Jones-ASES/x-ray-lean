import XRay.OneSidedCount

namespace XRay
open Finset

/-- Reflect rows and columns of a literal permutation matrix. -/
def reflectedPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  (Fin.revPerm.trans p).trans Fin.revPerm

@[simp] theorem reflectedPerm_involutive {n : ℕ} (p : Equiv.Perm (Fin n)) :
    reflectedPerm (reflectedPerm p) = p := by
  apply Equiv.ext
  intro i
  simp [reflectedPerm]

 theorem reflectedPerm_labels {n : ℕ} (p : Equiv.Perm (Fin n)) :
    labels (reflectedPerm p) = (labels p).map (fun z => 2 * (n : ℤ) - z) := by
  unfold labels
  conv_lhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simp only [Function.comp_def, reflectedPerm, Equiv.trans_apply, Fin.revPerm_apply,
    Fin.rev_rev, Fin.val_rev]
  have hi := i.isLt
  have hp := (p i).isLt
  omega

 theorem reflect_multiset {n : ℕ} (L : Profile n) :
    univ.val.map (reflect L) = (univ.val.map L).map (fun z => 2 * (n : ℤ) - z) := by
  conv_lhs => rw [← Multiset.map_univ_val_equiv Fin.revPerm, Multiset.map_map]
  rw [Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simp [reflect]

 theorem fiberCount_reflect_le {n : ℕ} (L : Profile n) : fiberCount (reflect L) ≤ fiberCount L := by
  classical
  let F := {p : Equiv.Perm (Fin n) // labels p = univ.val.map (reflect L)}
  let G := {p : Equiv.Perm (Fin n) // labels p = univ.val.map L}
  let f : F → G := fun p => ⟨reflectedPerm p.val, by
    rw [reflectedPerm_labels, p.property, ← reflect_multiset, reflect_reflect]⟩
  apply Fintype.card_le_of_injective f
  intro p q he
  have hh : reflectedPerm p.val = reflectedPerm q.val := congrArg (fun x : G => x.val) he
  apply Subtype.ext
  simpa only [reflectedPerm_involutive] using congrArg reflectedPerm hh

 theorem one_sided_upper_count {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, deviation L i ≤ 1) : 2 ^ negativeCount L ≤ fiberCount L := by
  have hlow := one_sided_lower_count hn (reflect L) hL.reflect (by
    intro i
    rw [deviation_reflect]
    have hh := hd i.rev
    omega)
  rw [positiveCount_reflect] at hlow
  exact hlow.trans (fiberCount_reflect_le L)

end XRay
