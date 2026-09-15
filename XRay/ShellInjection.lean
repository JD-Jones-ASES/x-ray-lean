import XRay.ShellMatrix

namespace XRay
open Finset

 theorem shell_core_label_bounds {n : ℕ} {p : Equiv.Perm (Fin n)}
    (hp : ∀ i, 2 ≤ cellProfile p i ∧ cellProfile p i ≤ 2 * (n : ℤ) - 2)
    (P : Finset ℤ) {x : ℤ} (hx : x ∈ board n) :
    4 ≤ switchedRow P (shifted p) x + switchedCol P (shifted p) x - 1 ∧
      switchedRow P (shifted p) x + switchedCol P (shifted p) x - 1 ≤ 2 * (n : ℤ) := by
  obtain ⟨i, rfl⟩ := mem_board_indices hx
  rw [switched_label, shifted_apply]
  have hh := hp i
  simp only [cellProfile] at hh
  constructor <;> omega

 theorem shell_low_unique {n : ℕ} (hn : 2 ≤ n) {p : Equiv.Perm (Fin n)}
    (hp : ∀ i, 2 ≤ cellProfile p i ∧ cellProfile p i ≤ 2 * (n : ℤ) - 2)
    (P : Finset ℤ) (s t : ℤ) {z : ℤ × ℤ}
    (hz : z ∈ shellCells p P s t) (hl : z.1 + z.2 - 1 = 3) : z = (1 - t, t + 3) := by
  rcases Multiset.mem_add.mp hz with hz | hz
  · rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
      have hb := (shell_core_label_bounds hp P hx).1
      dsimp at hl
      omega
    · simpa using hz
  · have he : z = (s + 2, 2 * (n : ℤ) - s) := by simpa using hz
    rw [he] at hl
    dsimp at hl
    omega

 theorem shell_high_unique {n : ℕ} (hn : 2 ≤ n) {p : Equiv.Perm (Fin n)}
    (hp : ∀ i, 2 ≤ cellProfile p i ∧ cellProfile p i ≤ 2 * (n : ℤ) - 2)
    (P : Finset ℤ) (s t : ℤ) {z : ℤ × ℤ}
    (hz : z ∈ shellCells p P s t) (hl : z.1 + z.2 - 1 = 2 * (n : ℤ) + 1) :
    z = (s + 2, 2 * (n : ℤ) - s) := by
  rcases Multiset.mem_add.mp hz with hz | hz
  · rcases Multiset.mem_add.mp hz with hz | hz
    · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hz
      have hb := (shell_core_label_bounds hp P hx).2
      dsimp at hl
      omega
    · have he : z = (1 - t, t + 3) := by simpa using hz
      rw [he] at hl
      dsimp at hl
      omega
  · simpa using hz

/-- For interior source labels, the target cells identify the endpoints,
then the rooted switch identifies the entire source permutation. -/
theorem shellCells_injective {n : ℕ} (hn : 2 ≤ n) {p q : Equiv.Perm (Fin n)}
    (_hp : ∀ i, 2 ≤ cellProfile p i ∧ cellProfile p i ≤ 2 * (n : ℤ) - 2)
    (hq : ∀ i, 2 ≤ cellProfile q i ∧ cellProfile q i ≤ 2 * (n : ℤ) - 2)
    {s t u v : ℤ} (hs : s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1)
    (P : RootedPath (board n) (shifted p) s t)
    (Q : RootedPath (board n) (shifted q) u v)
    (heq : shellCells p P.vertices s t = shellCells q Q.vertices u v) : p = q := by
  have hlow : (1 - t, t + 3) ∈ shellCells q Q.vertices u v := by
    rw [← heq]
    simp [shellCells]
  have hhigh : (s + 2, 2 * (n : ℤ) - s) ∈ shellCells q Q.vertices u v := by
    rw [← heq]
    simp [shellCells]
  have ht : t = v := by
    have hh := congrArg Prod.snd (shell_low_unique hn hq Q.vertices u v hlow (by dsimp; ring))
    dsimp at hh
    omega
  have hsu : s = u := by
    have hh := congrArg Prod.fst (shell_high_unique hn hq Q.vertices u v hhigh (by dsimp; ring))
    dsimp at hh
    omega
  subst u
  subst v
  have he : (board n).val.map (fun x => (switchedRow P.vertices (shifted p) x,
        switchedCol P.vertices (shifted p) x)) =
      (board n).val.map (fun x => (switchedRow Q.vertices (shifted q) x,
        switchedCol Q.vertices (shifted q) x)) := add_right_cancel (add_right_cancel heq)
  have hunshift (R : Finset ℤ) (f : ℤ → ℤ) :
      (fun x => (switchedRow R f x - 2, switchedCol R f x - 3)) = switchPair R f := by
    funext x
    simp only [switchedRow, switchedCol, switchPair]
    split_ifs <;> simp
  have he' := congrArg (Multiset.map (fun z : ℤ × ℤ => (z.1 - 2, z.2 - 3))) he
  simp only [Multiset.map_map, Function.comp_def, hunshift] at he'
  have hs' : (n : ℤ) - 3 < s := by rcases hs with rfl | rfl <;> omega
  have hi := (rooted_switch_injective P Q (shifted_injective p) (shifted_injective q)
    (shifted_source p hs') (shifted_source q hs') he').2
  apply Equiv.ext
  intro i
  have hx : (i.val : ℤ) + 1 ∈ board n := by simp only [board, mem_Icc]; constructor <;> omega
  have hh := hi _ hx
  rw [shifted_apply, shifted_apply] at hh
  apply Fin.ext
  omega

/-- A target matrix together with its recoverable construction data. -/
def ShellExtension {n : ℕ} (p : Equiv.Perm (Fin n)) (q : Equiv.Perm (Fin (n + 2))) : Prop :=
  ∃ s t : ℤ, (s = (n : ℤ) - 2 ∨ s = (n : ℤ) - 1) ∧
    (t = -1 ∨ t = 0) ∧ ∃ P : RootedPath (board n) (shifted p) s t,
      matrixCells q = shellCells p P.vertices s t

 theorem exists_shellExtension {n : ℕ} (hn : 1 ≤ n) (p : Equiv.Perm (Fin n)) :
    ∃ q, ShellExtension p q := by
  obtain ⟨s, t, hs, ht, ⟨P⟩⟩ := eligible_rooted_shell_path hn p
  obtain ⟨q, hq⟩ := shellCells_matrix p hs ht P.toPathSupport
  exact ⟨q, s, t, hs, ht, P, hq⟩

 theorem ShellExtension.labels {n : ℕ} {p : Equiv.Perm (Fin n)}
    {q : Equiv.Perm (Fin (n + 2))} (h : ShellExtension p q) :
    labels q = (labels p).map (fun z => z + 2) + {3} + {2 * (n : ℤ) + 1} := by
  obtain ⟨s, t, _, _, P, he⟩ := h
  rw [← matrixCells_labels, he, shellCells_labels]

 theorem ShellExtension.source_unique {n : ℕ} (hn : 2 ≤ n) {p r : Equiv.Perm (Fin n)}
    {q : Equiv.Perm (Fin (n + 2))}
    (hp : ∀ i, 2 ≤ cellProfile p i ∧ cellProfile p i ≤ 2 * (n : ℤ) - 2)
    (hr : ∀ i, 2 ≤ cellProfile r i ∧ cellProfile r i ≤ 2 * (n : ℤ) - 2)
    (h : ShellExtension p q) (h' : ShellExtension r q) : p = r := by
  obtain ⟨s, t, hs, _, P, he⟩ := h
  obtain ⟨u, v, _, _, Q, he'⟩ := h'
  exact shellCells_injective hn hp hr hs P Q (he.symm.trans he')

end XRay
