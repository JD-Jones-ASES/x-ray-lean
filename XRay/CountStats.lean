import XRay.Peeling
import XRay.Reflection

namespace XRay
open Finset

 theorem positiveCount_append {m n : ℕ} (A : Profile m) (B : Profile n) :
    positiveCount (append A B) = positiveCount A + positiveCount B := by
  classical
  simp only [positiveCount, card_filter, Fin.sum_univ_add,
    deviation_append_left, deviation_append_right]

 theorem positiveCount_reflect {n : ℕ} (L : Profile n) :
    positiveCount (reflect L) = negativeCount L := by
  classical
  simp only [positiveCount, negativeCount, card_filter, deviation_reflect, neg_pos]
  exact Equiv.sum_comp Fin.revPerm (fun i => if deviation L i < 0 then (1 : ℕ) else 0)

 theorem positiveCount_peel {m : ℕ} {L : Profile (m + 2)}
    (hfirst : 2 ≤ L 0) (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ)) :
    positiveCount L = positiveCount (peelLast L) + if L 0 = 2 then 1 else 0 := by
  classical
  have hf : 0 < deviation L 0 := by simp only [deviation, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]; omega
  have hl : ¬ 0 < deviation L (Fin.last (m + 1)) := by
    simp only [deviation, hlast, Fin.val_last, Nat.cast_add, Nat.cast_one]
    omega
  have hparent : positiveCount L = 1 +
      ∑ i : Fin m, if 0 < deviation L i.castSucc.succ then (1 : ℕ) else 0 := by
    unfold positiveCount
    rw [card_filter, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    simp only [if_pos hf, Fin.succ_last, if_neg hl, add_zero]
  have hchild : positiveCount (peelLast L) = (if 2 < L 0 then 1 else 0) +
      ∑ i : Fin m, if 0 < deviation L i.castSucc.succ then (1 : ℕ) else 0 := by
    unfold positiveCount
    rw [card_filter, Fin.sum_univ_succ]
    simp only [deviation_peelLast, Fin.val_zero, ite_true, Fin.castSucc_zero,
      Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false,
      sub_zero, Fin.castSucc_succ]
    have he : 0 < deviation L 0 - 1 ↔ 2 < L 0 := by
      simp only [deviation, Fin.val_zero, Nat.cast_zero, mul_zero, zero_add]
      omega
    simp only [he]
  rw [hparent, hchild]
  split_ifs <;> omega

end XRay
