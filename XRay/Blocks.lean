import XRay.Basic

namespace XRay
open Finset

/-- Put two profiles in successive diagonal blocks. -/
def append {m n : ℕ} (A : Profile m) (B : Profile n) : Profile (m + n) :=
  Fin.addCases A (fun i => B i + 2 * (m : ℤ))

/-- Direct sum of permutations, preserving the two coordinate intervals. -/
def blockPerm {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr p q)).trans finSumFinEquiv

@[simp] theorem blockPerm_left {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n))
    (i : Fin m) : blockPerm p q (i.castAdd n) = (p i).castAdd n := by
  simp [blockPerm]

@[simp] theorem blockPerm_right {m n : ℕ} (p : Equiv.Perm (Fin m)) (q : Equiv.Perm (Fin n))
    (i : Fin n) : blockPerm p q (i.natAdd m) = (q i).natAdd m := by
  simp [blockPerm]

 theorem Realizable.append {m n : ℕ} {A : Profile m} {B : Profile n}
    (hA : Realizable A) (hB : Realizable B) : Realizable (XRay.append A B) := by
  obtain ⟨r, c, hrc⟩ := hA
  obtain ⟨u, v, huv⟩ := hB
  refine ⟨blockPerm r u, blockPerm c v, fun i => ?_⟩
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [XRay.append, Fin.addCases_left, blockPerm_left, Fin.val_castAdd, hrc]
  · simp only [XRay.append, Fin.addCases_right, blockPerm_right, Fin.val_natAdd,
      Nat.cast_add, huv]
    ring

@[simp] theorem deviation_append_left {m n : ℕ} (A : Profile m) (B : Profile n) (i : Fin m) :
    deviation (append A B) (i.castAdd n) = deviation A i := by
  simp [deviation, append]

@[simp] theorem deviation_append_right {m n : ℕ} (A : Profile m) (B : Profile n) (i : Fin n) :
    deviation (append A B) (i.natAdd m) = deviation B i := by
  simp only [deviation, append, Fin.addCases_right, Fin.val_natAdd, Nat.cast_add]
  ring

 theorem card_prefix {n k : ℕ} (hk : k ≤ n) :
    (univ.filter (fun i : Fin n => i.val < k)).card = k := by
  by_cases hn : k < n
  · have hs : univ.filter (fun i : Fin n => i.val < k) = Iio (⟨k, hn⟩ : Fin n) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_Iio, Fin.lt_def]
    rw [hs, Fin.card_Iio]
  · have hkn : k = n := by omega
    subst k
    simp

 theorem slack_append_left {m n k : ℕ} (A : Profile m) (B : Profile n) (hk : k ≤ m) :
    slack (append A B) k = slack A k := by
  have hr (j : Fin n) : ¬ m + j.val < k := by omega
  simp only [slack, sum_filter, Fin.sum_univ_add, append, Fin.addCases_left,
    Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, hr, ite_false, sum_const_zero,
    add_zero]

 theorem slack_append_right {m n k : ℕ} (A : Profile m) (B : Profile n) (hk : k ≤ n) :
    slack (append A B) (m + k) = slack A m + slack B k := by
  have hl (i : Fin m) : i.val < m + k := by omega
  have hc (j : Fin n) : m + j.val < m + k ↔ j.val < k := by omega
  simp only [slack, sum_filter, Fin.sum_univ_add, append, Fin.addCases_left,
    Fin.addCases_right, Fin.val_castAdd, Fin.val_natAdd, hl, ite_true, hc,
    Fin.is_lt, Nat.cast_add]
  have hb : (∑ i : Fin n, if i.val < k then B i + 2 * (m : ℤ) else 0) =
      (∑ i : Fin n, if i.val < k then B i else 0) + (k : ℤ) * (2 * (m : ℤ)) := by
    rw [← sum_filter, sum_add_distrib, sum_const, nsmul_eq_mul, card_prefix hk, sum_filter]
  rw [hb]
  ring

/-- The first block at a prospective cut. -/
def leftBlock {m n : ℕ} (L : Profile (m + n)) : Profile m :=
  fun i => L (i.castAdd n)

/-- The second block, translated to start at the first board coordinate. -/
def rightBlock {m n : ℕ} (L : Profile (m + n)) : Profile n :=
  fun i => L (i.natAdd m) - 2 * (m : ℤ)

@[simp] theorem append_blocks {m n : ℕ} (L : Profile (m + n)) :
    append (leftBlock L) (rightBlock L) = L := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [append, leftBlock]
  · simp [append, rightBlock]

 theorem slack_leftBlock {m n k : ℕ} (L : Profile (m + n)) (hk : k ≤ m) :
    slack (leftBlock L) k = slack L k := by
  have h := slack_append_left (leftBlock L) (rightBlock L) hk
  simpa only [append_blocks] using h.symm

 theorem slack_rightBlock {m n k : ℕ} (L : Profile (m + n)) (hk : k ≤ n) :
    slack (rightBlock L) k = slack L (m + k) - slack L m := by
  have h := slack_append_right (leftBlock L) (rightBlock L) hk
  rw [append_blocks, slack_leftBlock L (Nat.le_refl m)] at h
  linarith

 theorem label_le_at_zero_cut {n k : ℕ} {L : Profile n} (h : Admissible L)
    (hk : k ≤ n) (hz : slack L k = 0) (i : Fin n) (hi : i.val < k) :
    L i ≤ 2 * (k : ℤ) - 1 := by
  have hk0 : 0 < k := by omega
  have hk' : k - 1 < n := by omega
  let j : Fin n := ⟨k - 1, hk'⟩
  have hs := slack_succ L hk'
  have he : k - 1 + 1 = k := by omega
  rw [he, hz] at hs
  have hp := h.2.2.1 (k - 1) (by omega)
  have hij : i ≤ j := by change i.val ≤ k - 1; omega
  have hl := h.1.monotone hij
  change 0 = slack L (k - 1) + (L j - (2 * ((k - 1 : ℕ) : ℤ) + 1)) at hs
  omega

 theorem label_ge_at_zero_cut {n k : ℕ} {L : Profile n} (h : Admissible L)
    (hz : slack L k = 0) (i : Fin n) (hi : k ≤ i.val) :
    2 * (k : ℤ) + 1 ≤ L i := by
  have hk : k < n := by omega
  let j : Fin n := ⟨k, hk⟩
  have hs := slack_succ L hk
  rw [hz, zero_add] at hs
  have hp := h.2.2.1 (k + 1) (by omega)
  have hij : j ≤ i := hi
  have hl := h.1.monotone hij
  change slack L (k + 1) = L j - (2 * (k : ℤ) + 1) at hs
  omega

/-- Equality in a density inequality splits the profile into two admissible
profiles, without changing their local deviations. -/
theorem admissible_blocks {m n : ℕ} {L : Profile (m + n)} (h : Admissible L)
    (hz : slack L m = 0) : Admissible (leftBlock L) ∧ Admissible (rightBlock L) := by
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact h.1 (show i.castAdd n < j.castAdd n from hij)
    · intro i
      refine ⟨(h.2.1 (i.castAdd n)).1, ?_⟩
      exact label_le_at_zero_cut h (by omega) hz (i.castAdd n) i.isLt
    · intro k hk
      rw [slack_leftBlock L hk]
      exact h.2.2.1 k (by omega)
    · rw [slack_leftBlock L (Nat.le_refl m), hz]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      have hl := h.1 (show i.natAdd m < j.natAdd m from by
        change m + i.val < m + j.val; omega)
      dsimp [rightBlock]
      omega
    · intro i
      have hlo := label_ge_at_zero_cut h hz (i.natAdd m) (by simp)
      have hhi := (h.2.1 (i.natAdd m)).2
      dsimp [rightBlock]
      push_cast at hhi
      constructor <;> omega
    · intro k hk
      rw [slack_rightBlock L hk, hz, sub_zero]
      exact h.2.2.1 _ (by omega)
    · rw [slack_rightBlock L (Nat.le_refl n), h.2.2.2, hz, sub_self]

end XRay
