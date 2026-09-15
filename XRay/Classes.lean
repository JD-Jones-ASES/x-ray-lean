import XRay.CutReduction
import XRay.Expanded
import XRay.DeepCore
import XRay.Reflection

namespace XRay

 theorem Fits.reflect {n : ℕ} {D : ℤ → Prop} {L : Profile n}
    (h : Fits D L) (hneg : ∀ d, D d → D (-d)) : Fits D (XRay.reflect L) := by
  intro i
  rw [deviation_reflect]
  exact hneg _ (h i.rev)

 theorem Primitive.reflect {n : ℕ} {L : Profile n} (h : Primitive L) (hL : Admissible L) :
    Primitive (XRay.reflect L) := by
  intro k hk0 hkn
  rw [slack_reflect L (by omega), hL.2.2.2, sub_zero]
  exact h (n - k) (by omega) (by omega)

 theorem fits_peelLast {m : ℕ} {D : ℤ → Prop} {L : Profile (m + 1)}
    (hD : Fits D L) (hband : ∀ d : ℤ, -2 ≤ d → d ≤ 2 → D d)
    (hfirst : 2 ≤ L 0 ∧ L 0 ≤ 3) : Fits D (peelLast L) := by
  intro i
  rw [deviation_peelLast]
  by_cases hi : i.val = 0
  · have he : i.castSucc = (0 : Fin (m + 1)) := Fin.ext hi
    rw [if_pos hi, he]
    apply hband
    · simp only [deviation, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]; omega
    · simp only [deviation, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]; omega
  · rw [if_neg hi, sub_zero]
    exact hD i.castSucc

 theorem fits_deepCore {m : ℕ} {D : ℤ → Prop} {L : Profile (m + 2)}
    (hD : Fits D L) : Fits D (deepCore L) := by
  intro i
  rw [deviation_deepCore]
  exact hD i.succ.castSucc

 theorem fits_expand {m : ℕ} (hm : 0 < m) {D : ℤ → Prop} {L : Profile (m + 1)}
    (hD : Fits D L) (hband : ∀ d : ℤ, -2 ≤ d → d ≤ 2 → D d)
    (hfirst : L 0 = 3) (hlast : L (Fin.last m) = 2 * (m : ℤ) - 1) :
    Fits D (expandExtremes L) := by
  intro i
  rw [deviation_expand]
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    have him : i.val ≠ m := by omega
    rw [if_pos hi, if_neg him, add_zero, he]
    have hd : deviation L 0 - 1 = 1 := by simp [deviation, hfirst]
    rw [hd]
    exact hband 1 (by omega) (by omega)
  · by_cases hj : i.val = m
    · have he : i = Fin.last m := Fin.ext hj
      rw [if_neg hi, sub_zero, if_pos hj, he]
      have hd : deviation L (Fin.last m) + 1 = -1 := by
        simp only [deviation, hlast, Fin.val_last]
        ring
      rw [hd]
      exact hband (-1) (by omega) (by omega)
    · rw [if_neg hi, sub_zero, if_neg hj, add_zero]
      exact hD i

end XRay
