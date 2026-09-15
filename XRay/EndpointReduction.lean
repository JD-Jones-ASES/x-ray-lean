import XRay.Classes

namespace XRay

/-- The order-one admissible profile is the identity profile. -/
theorem realizable_order_one {L : Profile 1} (h : Admissible L) : Realizable L := by
  refine ⟨Equiv.refl _, Equiv.refl _, fun i => ?_⟩
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have hh := h.2.1 0
  simp only [Equiv.refl_apply, Fin.val_zero, Nat.cast_zero, zero_add]
  norm_num at hh
  omega

/-- Case one, stated separately so reflection never recurses at the same order. -/
theorem realize_peel_case {m : ℕ} {D : ℤ → Prop} {L : Profile (m + 2)}
    (hband : ∀ d : ℤ, -2 ≤ d → d ≤ 2 → D d)
    (hL : Admissible L) (hP : Primitive L) (hD : Fits D L)
    (hfirst : L 0 ≤ 3) (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ))
    (ih : ∀ r < m + 2, ∀ K : Profile r, Admissible K → Fits D K → Realizable K) :
    Realizable L := by
  have hA := admissible_peelLast (by omega : 0 < m + 1) hL hP hlast
  have hF := fits_peelLast hD hband ⟨primitive_first (by omega) hP, hfirst⟩
  exact peelLast_restores hfirst hlast (ih (m + 1) (by omega) (peelLast L) hA hF)

/-- Endpoint reduction in any reflection-invariant deviation class containing
[-2,2]. The smaller-profile premise is discharged by induction in the main
theorem, and by minimality in the counterexample restriction. -/
theorem endpoint_reduction {n : ℕ} (hn : 1 ≤ n) {D : ℤ → Prop}
    (hband : ∀ d : ℤ, -2 ≤ d → d ≤ 2 → D d)
    (hneg : ∀ d, D d → D (-d))
    (ih : ∀ m < n, ∀ K : Profile m, Admissible K → Fits D K → Realizable K)
    (L : Profile n) (hL : Admissible L) (hD : Fits D L)
    (hfirst : L ⟨0, hn⟩ ≤ 3)
    (hlast : 2 * (n : ℤ) - 3 ≤ L ⟨n - 1, by omega⟩) : Realizable L := by
  cases n with
  | zero => omega
  | succ q =>
    cases q with
    | zero => exact realizable_order_one hL
    | succ m =>
      have hlo : L 0 ≤ 3 := by simpa only [Fin.mk_zero] using hfirst
      have hhi : 2 * (m : ℤ) + 1 ≤ L (Fin.last (m + 1)) := by
        have he : (⟨m + 1 + 1 - 1, by omega⟩ : Fin (m + 1 + 1)) = Fin.last (m + 1) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        rw [he] at hlast
        push_cast at hlast
        omega
      by_cases hP : Primitive L
      · have hf := primitive_first (by omega : 0 < m + 1) hP
        have hh : L (Fin.last (m + 1)) ≤ 2 * (m + 1 : ℤ) := by
          have hs := slack_succ L (show m + 1 < m + 2 by omega)
          rw [hL.2.2.2] at hs
          have hp := hP (m + 1) (by omega) (by omega)
          change 0 = slack L (m + 1) + (L (Fin.last (m + 1)) - (2 * (m + 1 : ℤ) + 1)) at hs
          omega
        by_cases he : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ)
        · exact realize_peel_case hband hL hP hD hlo he ih
        · have hlast' : L (Fin.last (m + 1)) = 2 * (m : ℤ) + 1 := by omega
          by_cases hfirst' : L 0 = 2
          · have hR := hL.reflect
            have hRP := hP.reflect hL
            have hRD := hD.reflect hneg
            have hrlo : reflect L 0 ≤ 3 := by
              simp only [reflect, Fin.rev_zero, hlast']
              push_cast
              omega
            have hrhi : reflect L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ) := by
              simp only [reflect, Fin.rev_last, hfirst']
              push_cast
              ring
            have hr := realize_peel_case hband hR hRP hRD hrlo hrhi ih
            simpa only [reflect_reflect] using hr.reflect
          · have hfirst' : L 0 = 3 := by omega
            by_cases hdeep : ∀ k, 0 < k → k < m + 2 → 2 ≤ slack L k
            · obtain ⟨hA, _⟩ := admissible_deepCore hL hfirst' hlast' hdeep
              have hFit := fits_deepCore hD
              have hReal := ih m (by omega) (deepCore L) hA hFit
              have hm : 1 ≤ m := by
                have hlt := hL.1 (show (0 : Fin (m + 2)) < Fin.last (m + 1) by change 0 < m + 1; omega)
                rw [hfirst', hlast'] at hlt
                omega
              exact deepCore_restores hm hfirst' hlast' hReal
            · push Not at hdeep
              obtain ⟨k, hk0, hkn, hk⟩ := hdeep
              have hz : slack L k = 1 := by have hp := hP k hk0 hkn; omega
              have hlast'' : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ) - 1 := by omega
              have hA := admissible_expand hL hP (by omega) (by omega)
              have hFit := fits_expand (by omega : 0 < m + 1) hD hband hfirst' hlast''
              have hz' : slack (expandExtremes L) k = 0 := by
                rw [slack_expand L (by omega), if_pos ⟨hk0, hkn⟩, hz, sub_self]
              have hlow' : expandExtremes L 0 = 2 := by
                simp [expandExtremes, hfirst']
              have hhigh' : expandExtremes L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ) := by
                simp only [expandExtremes, hlast', Fin.val_last, Nat.add_eq_zero_iff,
                  Nat.one_ne_zero, and_false, ite_false, sub_zero, ite_true]
                ring
              have hr := compress_at_cut hk0 hkn hz' hA hFit hlow' hhigh' ih
              simpa only [compress_expand] using hr
      · unfold Primitive at hP
        push Not at hP
        obtain ⟨k, hk0, hkn, hk⟩ := hP
        have hz : slack L k = 0 := by
          have hp := hL.2.2.1 k (by omega)
          omega
        exact realize_at_cut hk0 hkn hz hL hD ih

end XRay
