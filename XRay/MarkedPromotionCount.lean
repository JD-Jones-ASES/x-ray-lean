import XRay.CountedFibers

namespace XRay
open Finset

/-- Promotion lands in the parent's marked fiber, for either recorded orientation. -/
theorem marked_promotion_output {m : ℕ} {L : Profile (m + 2)}
    (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ))
    {p : Equiv.Perm (Fin (m + 1))} {q : Equiv.Perm (Fin (m + 2))}
    (hp : labels p = univ.val.map (peelLast L))
    (hp0 : (p 0).val + (1 : ℤ) = peelLast L 0)
    (hq : OrientedPromotion p q) (b : Bool) :
    labels (transposeBit b q) = univ.val.map L ∧ HasMinEdge L (transposeBit b q) := by
  have hlowp : (p 0).val + (1 : ℤ) = L 0 - 1 := by
    simpa only [peelLast, Fin.castSucc_zero, Fin.val_zero, ite_true] using hp0
  have hhighp : (p 0).val + (2 : ℤ) = L 0 := by omega
  have hprom := hq.labels
  rw [hp, hlowp, hhighp, ← hlast, peelLast_multiset L] at hprom
  have heq := add_right_cancel hprom
  refine ⟨by rw [labels_transposeBit]; exact heq, ?_⟩
  apply HasMinEdge.transposeBit _ b
  apply HasMinEdge.of_first
  exact Or.inl (by simpa only [hhighp] using hq.low)

/-- Normalization records its transposition bit in the output, preserving
all source matrices even when their minimum edge has either direction. -/
theorem anchoredCount_peel_preserved {m : ℕ} (hm : 1 ≤ m) {L : Profile (m + 2)}
    (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ)) :
    anchoredCount (peelLast L) ≤ anchoredCount L := by
  classical
  let F := MarkedFiber (peelLast L)
  let bit (p : F) : Bool := Classical.choose p.property.2.normalize
  let norm (p : F) : Equiv.Perm (Fin (m + 1)) := transposeBit (bit p) p.val
  have hn (p : F) : (norm p 0).val + (1 : ℤ) = peelLast L 0 :=
    Classical.choose_spec p.property.2.normalize
  let out (p : F) : Equiv.Perm (Fin (m + 2)) :=
    Classical.choose (exists_orientedPromotion hm (norm p))
  have ho (p : F) : OrientedPromotion (norm p) (out p) :=
    Classical.choose_spec (exists_orientedPromotion hm (norm p))
  let f : F → MarkedFiber L := fun p => ⟨transposeBit (bit p) (out p),
    marked_promotion_output hlast (by simpa only [norm, labels_transposeBit] using p.property.1)
      (hn p) (ho p) (bit p)⟩
  have hf : Function.Injective f := by
    intro p r he
    have hzero : norm p 0 = norm r 0 := by
      have hp := hn p
      have hr := hn r
      apply Fin.ext
      omega
    have he' : transposeBit (bit p) (out p) = transposeBit (bit r) (out r) := congrArg Subtype.val he
    obtain ⟨hpr, hbit⟩ := promotion_bits_injective hm hzero (ho p) (ho r) (bit p) (bit r) he'
    apply Subtype.ext
    have hh := congrArg (transposeBit (bit p)) hpr
    simpa only [norm, ← hbit, transposeBit_involutive] using hh
  exact Fintype.card_le_of_injective f hf

/-- A loop minimum needs no normalization, leaving both output orientations
available for each source matrix. -/
theorem anchoredCount_peel_doubled {m : ℕ} (hm : 1 ≤ m) {L : Profile (m + 2)}
    (hfirst : L 0 = 2) (hlast : L (Fin.last (m + 1)) = 2 * (m + 1 : ℤ)) :
    2 * anchoredCount (peelLast L) ≤ anchoredCount L := by
  classical
  let F := MarkedFiber (peelLast L)
  have hmin : peelLast L 0 = 1 := by simp [peelLast, hfirst]
  have hzero (p : F) : p.val 0 = 0 := by
    have hh := p.property.2 0 rfl
    rw [hmin] at hh
    have he : (1, (1 : ℤ)) ∈ matrixCells p.val := hh.elim id id
    have hv := (first_cell_iff p.val 1).mp he
    apply Fin.ext
    change (p.val 0).val = 0
    omega
  let out (p : F) : Equiv.Perm (Fin (m + 2)) :=
    Classical.choose (exists_orientedPromotion hm p.val)
  have ho (p : F) : OrientedPromotion p.val (out p) :=
    Classical.choose_spec (exists_orientedPromotion hm p.val)
  let f : F × Bool → MarkedFiber L := fun z => ⟨transposeBit z.2 (out z.1),
    marked_promotion_output hlast z.1.property.1
      (by rw [hzero z.1, hmin]; rfl) (ho z.1) z.2⟩
  have hf : Function.Injective f := by
    intro p r he
    have hz : p.1.val 0 = r.1.val 0 := (hzero p.1).trans (hzero r.1).symm
    have hh := promotion_bits_injective hm hz (ho p.1) (ho r.1) p.2 r.2 (congrArg Subtype.val he)
    exact Prod.ext (Subtype.ext hh.1) hh.2
  simpa only [anchoredCount, Fintype.card_prod, Fintype.card_bool, mul_comm] using
    Fintype.card_le_of_injective f hf

end XRay
