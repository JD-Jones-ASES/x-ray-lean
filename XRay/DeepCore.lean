import XRay.Peeling
import XRay.Extension

namespace XRay

/-- Remove both extreme labels and shift the middle labels down by two. -/
def deepCore {m : ℕ} (L : Profile (m + 2)) : Profile m :=
  fun i => L i.succ.castSucc - 2

 theorem deviation_deepCore {m : ℕ} (L : Profile (m + 2)) (i : Fin m) :
    deviation (deepCore L) i = deviation L i.succ.castSucc := by
  simp only [deviation, deepCore, Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  ring

 theorem slack_deepCore {m k : ℕ} (L : Profile (m + 2)) (hfirst : L 0 = 3) (hk : k ≤ m) :
    slack (deepCore L) k = slack L (k + 1) - 2 := by
  induction k with
  | zero =>
    have hs := slack_succ L (show 0 < m + 2 by omega)
    simp only [slack_zero, deviation, Nat.cast_zero, mul_zero, zero_add] at hs
    change slack L 1 = L 0 - 1 at hs
    rw [hfirst] at hs
    rw [slack_zero, hs]
    norm_num
  | succ k ih =>
    have hkm : k < m := by omega
    have hkn : k + 1 < m + 2 := by omega
    rw [slack_succ _ hkm, ih (by omega), deviation_deepCore, slack_succ _ hkn]
    have he : (⟨k, hkm⟩ : Fin m).succ.castSucc = (⟨k + 1, hkn⟩ : Fin (m + 2)) := Fin.ext rfl
    rw [he]
    ring

/-- The deep primitive reduction gives an admissible interior core. -/
theorem admissible_deepCore {m : ℕ} {L : Profile (m + 2)} (h : Admissible L)
    (hfirst : L 0 = 3) (hlast : L (Fin.last (m + 1)) = 2 * (m : ℤ) + 1)
    (hdeep : ∀ k, 0 < k → k < m + 2 → 2 ≤ slack L k) :
    Admissible (deepCore L) ∧ (∀ i, 2 ≤ deepCore L i ∧ deepCore L i ≤ 2 * (m : ℤ) - 2) := by
  have hrange (i : Fin m) : 2 ≤ deepCore L i ∧ deepCore L i ≤ 2 * (m : ℤ) - 2 := by
    have hlo := h.1 (show (0 : Fin (m + 2)) < i.succ.castSucc by change 0 < i.val + 1; omega)
    have hhi := h.1 (show i.succ.castSucc < Fin.last (m + 1) by
      change i.val + 1 < m + 1; omega)
    rw [hfirst] at hlo
    rw [hlast] at hhi
    change 2 ≤ L i.succ.castSucc - 2 ∧ L i.succ.castSucc - 2 ≤ 2 * (m : ℤ) - 2
    constructor <;> omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hrange⟩
  · intro i j hij
    have hl := h.1 (show i.succ.castSucc < j.succ.castSucc by
      change i.val + 1 < j.val + 1; omega)
    change L i.succ.castSucc - 2 < L j.succ.castSucc - 2
    omega
  · intro i
    have hr := hrange i
    constructor <;> omega
  · intro k hk
    rw [slack_deepCore L hfirst hk]
    have hs := hdeep (k + 1) (by omega) (by omega)
    omega
  · rw [slack_deepCore L hfirst (Nat.le_refl m)]
    have hs := slack_succ L (show m + 1 < m + 2 by omega)
    rw [h.2.2.2] at hs
    have he : (⟨m + 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := rfl
    rw [he] at hs
    simp only [deviation, hlast, Fin.val_last, Nat.cast_add, Nat.cast_one] at hs
    omega

theorem deepCore_restores {m : ℕ} (hm : 1 ≤ m) {L : Profile (m + 2)}
    (hfirst : L 0 = 3) (hlast : L (Fin.last (m + 1)) = 2 * (m : ℤ) + 1)
    (hc : Realizable (deepCore L)) : Realizable L := by
  apply (ordinary_extension hm hc).of_multiset
  rw [extend_multiset, Multiset.map_map]
  have he : (fun i : Fin m => deepCore L i + 2) = (fun i => L i.castSucc.succ) := by
    funext i
    have hi : i.succ.castSucc = i.castSucc.succ := Fin.ext rfl
    simp only [deepCore, sub_add_cancel, hi]
  change Finset.univ.val.map L = Finset.univ.val.map (fun i => deepCore L i + 2) + _ + _
  rw [he, Fin.univ_val_map, List.ofFn_succ, List.ofFn_succ_last]
  simp only [hfirst, Fin.succ_last, hlast, ← Multiset.cons_coe, ← Multiset.coe_add,
    ← Multiset.singleton_add, Fin.univ_val_map]
  ac_rfl

end XRay
