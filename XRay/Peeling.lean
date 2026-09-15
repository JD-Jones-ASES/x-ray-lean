import XRay.Blocks
import XRay.Promotion

namespace XRay

/-- Positive internal density slacks. -/
def Primitive {n : ℕ} (L : Profile n) : Prop :=
  ∀ k, 0 < k → k < n → 0 < slack L k

/-- Remove the last label and lower the first label by one. -/
def peelLast {m : ℕ} (L : Profile (m + 1)) : Profile m :=
  fun i => L i.castSucc - if i.val = 0 then 1 else 0

 theorem deviation_peelLast {m : ℕ} (L : Profile (m + 1)) (i : Fin m) :
    deviation (peelLast L) i = deviation L i.castSucc - if i.val = 0 then 1 else 0 := by
  simp only [deviation, peelLast, Fin.val_castSucc]
  ring

 theorem slack_peelLast {m k : ℕ} (L : Profile (m + 1)) (hk : k ≤ m) :
    slack (peelLast L) k = slack L k - if k = 0 then 0 else 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m := by omega
    have hkn : k < m + 1 := by omega
    rw [slack_succ _ hkm, ih (by omega), deviation_peelLast, slack_succ _ hkn]
    have he : (⟨k, hkm⟩ : Fin m).castSucc = (⟨k, hkn⟩ : Fin (m + 1)) := Fin.ext rfl
    rw [he]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    split_ifs <;> ring

 theorem primitive_first {m : ℕ} (hm : 0 < m) {L : Profile (m + 1)}
    (h : Primitive L) : 2 ≤ L 0 := by
  have hs := slack_succ L (show 0 < m + 1 by omega)
  have hp := h 1 (by omega) (by omega)
  simp only [slack_zero, deviation, Nat.cast_zero, mul_zero, zero_add] at hs
  change slack L 1 = L 0 - 1 at hs
  omega

/-- The primitive final-deviation-minus-one reduction preserves admissibility. -/
theorem admissible_peelLast {m : ℕ} (hm : 0 < m) {L : Profile (m + 1)}
    (h : Admissible L) (hp : Primitive L) (hlast : L (Fin.last m) = 2 * (m : ℤ)) :
    Admissible (peelLast L) := by
  have hfirst := primitive_first hm hp
  have hz : slack L m = 1 := by
    have hs := slack_succ L (show m < m + 1 by omega)
    rw [h.2.2.2] at hs
    have he : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
    rw [he] at hs
    simp only [deviation, hlast, Fin.val_last] at hs
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hlt := h.1 (show i.castSucc < j.castSucc from hij)
    have hj : j.val ≠ 0 := by have hv : i.val < j.val := hij; omega
    simp only [peelLast, if_neg hj, sub_zero]
    split_ifs <;> omega
  · intro i
    have hlt := h.1 (show i.castSucc < Fin.last m from i.isLt)
    rw [hlast] at hlt
    have hlo := (h.2.1 i.castSucc).1
    dsimp [peelLast]
    by_cases hi : i.val = 0
    · have he : i.castSucc = (0 : Fin (m + 1)) := Fin.ext hi
      rw [if_pos hi, he]
      rw [he] at hlt
      constructor <;> omega
    · rw [if_neg hi, sub_zero]
      constructor <;> omega
  · intro k hk
    rw [slack_peelLast L hk]
    by_cases hk0 : k = 0
    · subst k; simp
    · rw [if_neg hk0]
      have hs := hp k (by omega) (by omega)
      omega
  · rw [slack_peelLast L (Nat.le_refl m), if_neg (by omega), hz, sub_self]

theorem peelLast_multiset {m : ℕ} (L : Profile (m + 2)) :
    Finset.univ.val.map (peelLast L) + {L 0} + {L (Fin.last (m + 1))} =
      Finset.univ.val.map L + {L 0 - 1} := by
  have hL : Finset.univ.val.map L =
      {L 0} + Finset.univ.val.map (fun i : Fin m => L i.castSucc.succ) +
        {L (Fin.last (m + 1))} := by
    rw [Fin.univ_val_map, List.ofFn_succ, List.ofFn_succ_last]
    simp only [Fin.succ_last, ← Multiset.cons_coe, ← Multiset.coe_add,
      Multiset.coe_nil, add_zero, ← Multiset.singleton_add, Fin.univ_val_map, add_assoc]
  have hK : Finset.univ.val.map (peelLast L) =
      {L 0 - 1} + Finset.univ.val.map (fun i : Fin m => L i.castSucc.succ) := by
    rw [Fin.univ_val_map, List.ofFn_succ]
    simp only [peelLast, Fin.castSucc_zero, Fin.val_zero, ite_true, Fin.val_succ,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, sub_zero,
      Fin.castSucc_succ, ← Multiset.cons_coe, ← Multiset.singleton_add, Fin.univ_val_map]
  rw [hL, hK]
  ac_rfl

/-- Promotion restores the peeled profile whenever its minimum label is at
most two. This condition forces the required first-row cell. -/
theorem peelLast_restores {m : ℕ} {L : Profile (m + 2)}
    (hlow : L 0 ≤ 3) (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ))
    (h : Realizable (peelLast L)) : Realizable L := by
  have hk : peelLast L 0 ≤ 2 := by simp only [peelLast, Fin.castSucc_zero, Fin.val_zero, ite_true]; omega
  obtain ⟨p, hp, hp0⟩ := first_row_of_small_label h hk
  have hlowp : (p 0).val + (1 : ℤ) = L 0 - 1 := by
    simpa only [peelLast, Fin.castSucc_zero, Fin.val_zero, ite_true] using hp0
  have hhighp : (p 0).val + (2 : ℤ) = L 0 := by omega
  have hprom := promoted_multiset p
  rw [hp, hlowp, hhighp, ← hlast, peelLast_multiset L] at hprom
  have heq := add_right_cancel hprom
  exact (promoted_realizable p).of_multiset heq.symm

end XRay
