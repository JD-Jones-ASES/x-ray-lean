import XRay.EndpointReduction

namespace XRay

/-- The one-sided lower bound is preserved by primitive peeling. -/
theorem lower_peelLast {m : ℕ} (hm : 0 < m) {L : Profile (m + 1)}
    (hP : Primitive L) (hD : ∀ i, -1 ≤ deviation L i) :
    ∀ i, -1 ≤ deviation (peelLast L) i := by
  intro i
  rw [deviation_peelLast]
  by_cases hi : i.val = 0
  · have he : i.castSucc = (0 : Fin (m + 1)) := Fin.ext hi
    rw [if_pos hi, he]
    have hf := primitive_first hm hP
    simp only [deviation, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
    omega
  · rw [if_neg hi, sub_zero]
    exact hD i.castSucc

/-- A minimum-anchored child restores a minimum-anchored parent, without
an upper bound on the first deviation. -/
theorem peelLast_restores_min {m : ℕ} {L : Profile (m + 2)}
    (hL : StrictMono L) (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ))
    (h : MinAnchored (peelLast L)) : MinAnchored L := by
  obtain ⟨p, hp, hp0⟩ := h.first_row
  have hlowp : (p 0).val + (1 : ℤ) = L 0 - 1 := by
    simpa only [peelLast, Fin.castSucc_zero, Fin.val_zero, ite_true] using hp0
  have hhighp : (p 0).val + (2 : ℤ) = L 0 := by omega
  have hprom := promoted_multiset p
  rw [hp, hlowp, hhighp, ← hlast, peelLast_multiset L] at hprom
  have heq := add_right_cancel hprom
  obtain ⟨r, c, hrc, hz⟩ := promoted_marked p
  apply minAnchored_of_marked_multiset hL.injective heq.symm r c hrc
    ((0 : Fin 2).natAdd m) ?_ hz
  simpa only [promoted, Fin.addCases_right, Matrix.cons_val_zero] using hhighp

/-- The full one-sided family, strengthened to retain its minimum edge. -/
theorem one_sided_lower_anchored {n : ℕ} (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : MinAnchored L := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨Equiv.refl _, Equiv.refl _, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    | succ q =>
      cases q with
      | zero =>
        have hR := realizable_order_one hL
        obtain ⟨r, c, hrc⟩ := hR
        refine ⟨r, c, hrc, fun i _ => Or.inl ?_⟩
        exact (r i).isLt |> (fun h => by omega)
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
          have hA := admissible_peelLast (by omega : 0 < m + 1) hL hP hlast
          have hF := lower_peelLast (by omega : 0 < m + 1) hP hd
          exact peelLast_restores_min hL.1 hlast
            (ih (m + 1) (by omega) (peelLast L) hA hF)
        · unfold Primitive at hP
          push Not at hP
          obtain ⟨k, hk0, hkn, hk⟩ := hP
          have hz : slack L k = 0 := by
            have hp := hL.2.2.1 k (by omega)
            omega
          obtain ⟨a, ha⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
          obtain ⟨b, hb⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m + 2 - k ≠ 0)
          have hm : m + 2 = (a + 1) + (b + 1) := by omega
          -- Use a separate order-variable statement to avoid dependent successor rewriting.
          have aux {t : ℕ} (K : Profile t) (hK : Admissible K)
              (hF : Fits (fun d => -1 ≤ d) K)
              (hI : ∀ r < t, ∀ A : Profile r, Admissible A →
                (∀ i, -1 ≤ deviation A i) → MinAnchored A)
              (ht : t = (a + 1) + (b + 1))
              (hzero : slack K (a + 1) = 0) : MinAnchored K := by
            subst t
            obtain ⟨hA, hB⟩ := admissible_blocks (m := a + 1) (n := b + 1) hK hzero
            have hRA := hI (a + 1) (by omega)
              (leftBlock (m := a + 1) (n := b + 1) K) hA
              (fits_leftBlock (m := a + 1) (n := b + 1) hF)
            have hRB := hI (b + 1) (by omega)
              (rightBlock (m := a + 1) (n := b + 1) K) hB
              (fits_rightBlock (m := a + 1) (n := b + 1) hF)
            simpa only [append_blocks] using hRA.append (by omega) hRB.realizable
          exact aux L hL hd ih hm (by simpa only [ha] using hz)

 theorem one_sided_lower {n : ℕ} (_hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : Realizable L :=
  (one_sided_lower_anchored L hL hd).realizable

 theorem one_sided_upper {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, deviation L i ≤ 1) : Realizable L := by
  have hR : Realizable (reflect L) := one_sided_lower hn (reflect L) hL.reflect (by
    intro i
    rw [deviation_reflect]
    have h := hd i.rev
    omega)
  simpa only [reflect_reflect] using hR.reflect

end XRay
