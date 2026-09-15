import XRay.Peeling
import XRay.Compression

namespace XRay

/-- Lower the minimum label and raise the maximum label by one. -/
def expandExtremes {m : ℕ} (L : Profile (m + 1)) : Profile (m + 1) :=
  fun i => L i - (if i.val = 0 then 1 else 0) + (if i.val = m then 1 else 0)

@[simp] theorem compress_expand {m : ℕ} (L : Profile (m + 1)) :
    compressExtremes (expandExtremes L) = L := by
  funext i
  simp only [compressExtremes, expandExtremes]
  ring

 theorem deviation_expand {m : ℕ} (L : Profile (m + 1)) (i : Fin (m + 1)) :
    deviation (expandExtremes L) i = deviation L i - (if i.val = 0 then 1 else 0) +
      (if i.val = m then 1 else 0) := by
  simp only [deviation, expandExtremes]
  ring

 theorem slack_expand {m k : ℕ} (L : Profile (m + 1)) (hk : k ≤ m + 1) :
    slack (expandExtremes L) k = slack L k - if 0 < k ∧ k < m + 1 then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkm : k < m + 1 := by omega
    rw [slack_succ _ hkm, ih (by omega), deviation_expand, slack_succ _ hkm]
    simp only
    split_ifs <;> omega

 theorem admissible_expand {m : ℕ} {L : Profile (m + 1)} (h : Admissible L)
    (hp : Primitive L) (hfirst : 2 ≤ L 0) (hlast : L (Fin.last m) ≤ 2 * (m : ℤ)) :
    Admissible (expandExtremes L) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hlt := h.1 hij
    have hi : i.val ≠ m := by have hj := j.isLt; have hv : i.val < j.val := hij; omega
    have hj : j.val ≠ 0 := by have hv : i.val < j.val := hij; omega
    simp only [expandExtremes, if_neg hi, if_neg hj, sub_zero, add_zero]
    split_ifs <;> omega
  · intro i
    have hb := h.2.1 i
    have hf : i.val = 0 → 2 ≤ L i := by
      intro hi
      have he : i = 0 := Fin.ext hi
      simpa only [he] using hfirst
    have hl : i.val = m → L i ≤ 2 * (m : ℤ) := by
      intro hi
      have he : i = Fin.last m := Fin.ext hi
      simpa only [he] using hlast
    simp only [expandExtremes, Nat.cast_add, Nat.cast_one]
    split_ifs <;> constructor <;> omega
  · intro k hk
    rw [slack_expand L hk]
    by_cases hi : 0 < k ∧ k < m + 1
    · rw [if_pos hi]
      have hs := hp k hi.1 hi.2
      omega
    · rw [if_neg hi, sub_zero]
      exact h.2.2.1 k hk
  · rw [slack_expand L (Nat.le_refl _), if_neg (by omega), sub_zero, h.2.2.2]

 theorem deviation_expand_bound {m : ℕ} {L : Profile (m + 1)}
    (hfirst : L 0 = 3) (hlast : L (Fin.last m) = 2 * (m : ℤ) - 1)
    (hd : ∀ i, -2 ≤ deviation L i ∧ deviation L i ≤ 2) :
    ∀ i, -2 ≤ deviation (expandExtremes L) i ∧ deviation (expandExtremes L) i ≤ 2 := by
  intro i
  have hdi := hd i
  have hf : i.val = 0 → deviation L i = 2 := by
    intro hi
    have he : i = 0 := Fin.ext hi
    simp [he, deviation, hfirst]
  have hl : i.val = m → deviation L i = -2 := by
    intro hi
    have he : i = Fin.last m := Fin.ext hi
    simp only [he, deviation, hlast, Fin.val_last]
    ring
  rw [deviation_expand]
  split_ifs <;> constructor <;> omega

end XRay
