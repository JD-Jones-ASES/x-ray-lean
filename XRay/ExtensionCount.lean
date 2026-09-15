import XRay.ShellInjection

namespace XRay
open Finset

/-- Bounds on a label multiset apply to every cell in every member of its fiber. -/
theorem cellProfile_bounds_of_labels {n : ℕ} {L : Profile n} {a b : ℤ}
    (hL : ∀ i, a ≤ L i ∧ L i ≤ b) {p : Equiv.Perm (Fin n)}
    (hp : labels p = univ.val.map L) : ∀ i, a ≤ cellProfile p i ∧ cellProfile p i ≤ b := by
  intro i
  have hm : cellProfile p i ∈ univ.val.map L := by
    rw [← hp]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  obtain ⟨j, _, hj⟩ := Multiset.mem_map.mp hm
  rw [← hj]
  exact hL j

/-- Every interior label fiber injects into the fiber of its ordinary extension. -/
theorem extension_count {n : ℕ} (hn : 1 ≤ n) (L : Profile n)
    (hL : ∀ i, 2 ≤ L i ∧ L i ≤ 2 * (n : ℤ) - 2) :
    fiberCount L ≤ fiberCount (extend L) := by
  classical
  have hn2 : 2 ≤ n := by
    have hh := hL ⟨0, hn⟩
    omega
  let F := {p : Equiv.Perm (Fin n) // labels p = univ.val.map L}
  let G := {q : Equiv.Perm (Fin (n + 2)) // labels q = univ.val.map (extend L)}
  have hchoice (p : F) : ∃ q : G, ShellExtension p.val q.val := by
    obtain ⟨q, hq⟩ := exists_shellExtension hn p.val
    have hlabels : labels q = univ.val.map (extend L) := by
      rw [hq.labels, p.property, extend_multiset]
    exact ⟨⟨q, hlabels⟩, hq⟩
  let f : F → G := fun p => Classical.choose (hchoice p)
  have hf : Function.Injective f := by
    intro p r he
    have hp := Classical.choose_spec (hchoice p)
    have hr := Classical.choose_spec (hchoice r)
    change ShellExtension p.val (f p).val at hp
    change ShellExtension r.val (f r).val at hr
    rw [he] at hp
    apply Subtype.ext
    exact ShellExtension.source_unique hn2
      (cellProfile_bounds_of_labels hL p.property)
      (cellProfile_bounds_of_labels hL r.property) hp hr
  exact Fintype.card_le_of_injective f hf

end XRay
