import XRay.BlockAnchors

namespace XRay

/-- A class specified by a predicate on every rank deviation. -/
def Fits {n : ℕ} (D : ℤ → Prop) (L : Profile n) : Prop :=
  ∀ i, D (deviation L i)

 theorem fits_leftBlock {m n : ℕ} {D : ℤ → Prop} {L : Profile (m + n)}
    (h : Fits D L) : Fits D (leftBlock L) := by
  intro i
  exact h (i.castAdd n)

 theorem fits_rightBlock {m n : ℕ} {D : ℤ → Prop} {L : Profile (m + n)}
    (h : Fits D L) : Fits D (rightBlock L) := by
  intro i
  have he : deviation (rightBlock L) i = deviation L (i.natAdd m) := by
    simp only [deviation, rightBlock, Fin.val_natAdd, Nat.cast_add]
    ring
  rw [he]
  exact h (i.natAdd m)

 theorem realize_at_cut {n k : ℕ} {D : ℤ → Prop} {L : Profile n}
    (hk0 : 0 < k) (hkn : k < n) (hz : slack L k = 0)
    (hL : Admissible L) (hD : Fits D L)
    (ih : ∀ m < n, ∀ K : Profile m, Admissible K → Fits D K → Realizable K) :
    Realizable L := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n - k ≠ 0)
  have hn : n = (a + 1) + (b + 1) := by omega
  subst n
  subst k
  obtain ⟨hA, hB⟩ := admissible_blocks (m := a + 1) (n := b + 1) hL hz
  have hRA := ih (a + 1) (by omega) (leftBlock (m := a + 1) (n := b + 1) L) hA (fits_leftBlock (m := a + 1) (n := b + 1) hD)
  have hRB := ih (b + 1) (by omega) (rightBlock (m := a + 1) (n := b + 1) L) hB (fits_rightBlock (m := a + 1) (n := b + 1) hD)
  simpa only [append_blocks] using hRA.append hRB

/-- A zero cut with small extreme labels supplies both compression anchors. -/
theorem compress_at_cut {m k : ℕ} {D : ℤ → Prop} {L : Profile (m + 1)}
    (hk0 : 0 < k) (hkn : k < m + 1) (hz : slack L k = 0)
    (hL : Admissible L) (hD : Fits D L)
    (hfirst : L 0 = 2) (hlast : L (Fin.last m) = 2 * (m : ℤ))
    (ih : ∀ r < m + 1, ∀ K : Profile r, Admissible K → Fits D K → Realizable K) :
    Realizable (compressExtremes L) := by
  obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m + 1 - k ≠ 0)
  have hm : m = (a + 1) + b := by omega
  subst m
  subst k
  obtain ⟨hA, hB⟩ := admissible_blocks (m := a + 1) (n := b + 1) hL hz
  have hRA := ih (a + 1) (by omega) (leftBlock (m := a + 1) (n := b + 1) L) hA (fits_leftBlock (m := a + 1) (n := b + 1) hD)
  have hRB := ih (b + 1) (by omega) (rightBlock (m := a + 1) (n := b + 1) L) hB (fits_rightBlock (m := a + 1) (n := b + 1) hD)
  have hmin : leftBlock (m := a + 1) (n := b + 1) L 0 ≤ 2 := by
    change L 0 ≤ 2
    omega
  have hmax : 2 * (b : ℤ) ≤ rightBlock (m := a + 1) (n := b + 1) L (Fin.last b) := by
    change 2 * (b : ℤ) ≤ L (Fin.last ((a + 1) + b)) - 2 * ((a + 1 : ℕ) : ℤ)
    rw [hlast]
    push_cast
    omega
  simpa only [append_blocks] using compress_blocks hRA hRB hmin hmax

end XRay
