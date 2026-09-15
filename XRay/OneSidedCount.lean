import XRay.MarkedPromotionCount

namespace XRay

/-- The counted induction retains the minimum edge in every constructed matrix. -/
theorem one_sided_lower_anchored_count {n : ℕ} (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : 2 ^ positiveCount L ≤ anchoredCount L := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have hz : positiveCount L = 0 := by simp [positiveCount]
      rw [hz, pow_zero]
      exact one_le_anchoredCount (one_sided_lower_anchored L hL hd)
    | succ q =>
      cases q with
      | zero =>
        have hdev (i : Fin 1) : deviation L i = 0 := by
          have hh := hL.2.1 i
          have hi := i.isLt
          simp only [deviation]
          norm_num at hh
          omega
        have hz : positiveCount L = 0 := by simp [positiveCount, hdev]
        rw [hz, pow_zero]
        exact one_le_anchoredCount (one_sided_lower_anchored L hL hd)
      | succ m =>
        by_cases hP : Primitive L
        · have hs := slack_succ L (show m + 1 < m + 2 by omega)
          rw [hL.2.2.2] at hs
          have hp := hP (m + 1) (by omega) (by omega)
          have hdlast := hd (Fin.last (m + 1))
          have he : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := rfl
          rw [he] at hs
          have hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ) := by
            simp only [deviation, Fin.val_last, Nat.cast_add, Nat.cast_one] at hs hdlast
            omega
          have hfirst := primitive_first (by omega : 0 < m + 1) hP
          have hm : 1 ≤ m := by
            have hlt := hL.1 (show (0 : Fin (m + 2)) < Fin.last (m + 1) by change 0 < m + 1; omega)
            rw [hlast] at hlt
            omega
          have hA := admissible_peelLast (by omega : 0 < m + 1) hL hP hlast
          have hF := lower_peelLast (by omega : 0 < m + 1) hP hd
          have hI := ih (m + 1) (by omega) (peelLast L) hA hF
          rw [positiveCount_peel hfirst hlast]
          by_cases hf : L 0 = 2
          · rw [if_pos hf, pow_succ]
            calc
              _ ≤ 2 * anchoredCount (peelLast L) := by omega
              _ ≤ _ := anchoredCount_peel_doubled hm hf hlast
          · rw [if_neg hf, add_zero]
            exact hI.trans (anchoredCount_peel_preserved hm hlast)
        · unfold Primitive at hP
          push Not at hP
          obtain ⟨k, hk0, hkn, hk⟩ := hP
          have hz : slack L k = 0 := by
            have hp := hL.2.2.1 k (by omega)
            omega
          obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m + 2 - k ≠ 0)
          have hm : m + 2 = (a + 1) + (b + 1) := by omega
          have aux {t : ℕ} (K : Profile t) (hK : Admissible K)
              (hF : Fits (fun d => -1 ≤ d) K)
              (hI : ∀ r < t, ∀ A : Profile r, Admissible A →
                (∀ i, -1 ≤ deviation A i) → 2 ^ positiveCount A ≤ anchoredCount A)
              (ht : t = (a + 1) + (b + 1))
              (hzero : slack K (a + 1) = 0) : 2 ^ positiveCount K ≤ anchoredCount K := by
            subst t
            obtain ⟨hA, hB⟩ := admissible_blocks (m := a + 1) (n := b + 1) hK hzero
            have hRA := hI (a + 1) (by omega)
              (leftBlock (m := a + 1) (n := b + 1) K) hA
              (fits_leftBlock (m := a + 1) (n := b + 1) hF)
            have hRB := hI (b + 1) (by omega)
              (rightBlock (m := a + 1) (n := b + 1) K) hB
              (fits_rightBlock (m := a + 1) (n := b + 1) hF)
            have hp : positiveCount K =
                positiveCount (leftBlock (m := a + 1) (n := b + 1) K) +
                positiveCount (rightBlock (m := a + 1) (n := b + 1) K) := by
              simpa only [append_blocks] using
                positiveCount_append (leftBlock (m := a + 1) (n := b + 1) K)
                  (rightBlock (m := a + 1) (n := b + 1) K)
            rw [hp, pow_add]
            exact (Nat.mul_le_mul hRA hRB).trans (by
              simpa only [append_blocks] using anchoredCount_append (by omega : 0 < a + 1)
                (leftBlock (m := a + 1) (n := b + 1) K)
                (rightBlock (m := a + 1) (n := b + 1) K))
          exact aux L hL hd ih hm (by simpa only [ha] using hz)

 theorem one_sided_lower_count {n : ℕ} (_hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : 2 ^ positiveCount L ≤ fiberCount L :=
  (one_sided_lower_anchored_count L hL hd).trans (anchoredCount_le_fiberCount L)

end XRay
