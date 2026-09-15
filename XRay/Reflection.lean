import XRay.Basic

namespace XRay

/-- Reflect both board coordinates, and reverse the rank order. -/
def reflect {n : ℕ} (L : Profile n) : Profile n :=
  fun i => 2 * (n : ℤ) - L i.rev

@[simp] theorem reflect_reflect {n : ℕ} (L : Profile n) : reflect (reflect L) = L := by
  funext i
  simp [reflect]

 theorem deviation_reflect {n : ℕ} (L : Profile n) (i : Fin n) :
    deviation (reflect L) i = -deviation L i.rev := by
  simp only [deviation, reflect, Fin.val_rev]
  have hi := i.isLt
  omega

 theorem Realizable.reflect {n : ℕ} {L : Profile n} (h : Realizable L) :
    Realizable (reflect L) := by
  obtain ⟨r, c, hrc⟩ := h
  refine ⟨(Fin.revPerm.trans r).trans Fin.revPerm,
    (Fin.revPerm.trans c).trans Fin.revPerm, fun i => ?_⟩
  change 2 * (n : ℤ) - L i.rev = ((r i.rev).rev.val : ℤ) + (c i.rev).rev.val + 1
  rw [hrc]
  simp only [Fin.val_rev]
  have hr := (r i.rev).isLt
  have hc := (c i.rev).isLt
  omega

/-- Reflection reverses the slack sequence, up to its total slack. -/
theorem slack_reflect {n : ℕ} (L : Profile n) {k : ℕ} (hk : k ≤ n) :
    slack (reflect L) k = slack L (n - k) - slack L n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkn : k < n := by omega
    have hrem : n - (k + 1) < n := by omega
    rw [slack_succ _ hkn, ih (by omega), deviation_reflect]
    have heq : (⟨k, hkn⟩ : Fin n).rev = ⟨n - (k + 1), hrem⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
    rw [heq]
    have hs := slack_succ L hrem
    have hn : n - (k + 1) + 1 = n - k := by omega
    rw [hn] at hs
    linarith

 theorem Admissible.reflect {n : ℕ} {L : Profile n} (h : Admissible L) :
    Admissible (reflect L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hr : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    have hl := h.1 hr
    simp only [XRay.reflect]
    omega
  · intro i
    have hi := h.2.1 i.rev
    simp only [XRay.reflect]
    omega
  · intro k hk
    rw [slack_reflect L hk, h.2.2.2, sub_zero]
    exact h.2.2.1 _ (by omega)
  · rw [slack_reflect L (Nat.le_refl n), Nat.sub_self, slack_zero, h.2.2.2]
    rfl

end XRay
