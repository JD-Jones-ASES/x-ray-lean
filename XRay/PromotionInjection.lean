import XRay.PromotionMatrix

namespace XRay

/-- A promotion with its low edge oriented from vertex one. -/
def OrientedPromotion {m : ℕ} (p : Equiv.Perm (Fin (m + 1)))
    (q : Equiv.Perm (Fin (m + 2))) : Prop :=
  ∃ t : ℤ, (t = (m : ℤ) + 1 ∨ t = (m : ℤ) + 2) ∧
    ∃ P : RootedPath (board m) (promotionCore p) 1 t,
      matrixCells q = promotionCells p P.vertices t

 theorem exists_orientedPromotion {m : ℕ} (hm : 1 ≤ m) (p : Equiv.Perm (Fin (m + 1))) :
    ∃ q, OrientedPromotion p q := by
  obtain ⟨t, ht, ⟨P⟩⟩ := promotion_rooted_path hm p
  obtain ⟨q, hq⟩ := promotionCells_matrix p ht P.toPathSupport
  exact ⟨q, t, ht, P, hq⟩

 theorem OrientedPromotion.labels {m : ℕ} {p : Equiv.Perm (Fin (m + 1))}
    {q : Equiv.Perm (Fin (m + 2))} (h : OrientedPromotion p q) :
    labels q + {(p 0).val + (1 : ℤ)} =
      labels p + {(p 0).val + (2 : ℤ)} + {2 * (m + 1 : ℤ)} := by
  obtain ⟨t, _, P, he⟩ := h
  rw [← matrixCells_labels, he, promotionCells_labels]

 theorem OrientedPromotion.low {m : ℕ} {p : Equiv.Perm (Fin (m + 1))}
    {q : Equiv.Perm (Fin (m + 2))} (h : OrientedPromotion p q) :
    (1, (p 0).val + (2 : ℤ)) ∈ matrixCells q := by
  obtain ⟨t, _, P, he⟩ := h
  rw [he]
  simp [promotionCells]

 theorem OrientedPromotion.no_reverse {m : ℕ} (hm : 1 ≤ m)
    {p : Equiv.Perm (Fin (m + 1))} {q : Equiv.Perm (Fin (m + 2))}
    (h : OrientedPromotion p q) : ((p 0).val + (2 : ℤ), 1) ∉ matrixCells q := by
  obtain ⟨t, ht, P, he⟩ := h
  rw [he]
  exact promotionCells_no_reverse hm p P.vertices ht

 theorem OrientedPromotion.source_unique {m : ℕ} (hm : 1 ≤ m)
    {p r : Equiv.Perm (Fin (m + 1))} {q : Equiv.Perm (Fin (m + 2))}
    (hzero : p 0 = r 0) (hp : OrientedPromotion p q) (hr : OrientedPromotion r q) : p = r := by
  obtain ⟨s, _, P, he⟩ := hp
  obtain ⟨t, _, Q, he'⟩ := hr
  exact promotionCells_injective hm hzero P Q (he.symm.trans he')

/-- Reversing every edge preserves labels and records a Boolean choice. -/
def transposeBit {n : ℕ} (b : Bool) (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  if b then p.symm else p

@[simp] theorem transposeBit_false {n : ℕ} (p : Equiv.Perm (Fin n)) :
    transposeBit false p = p := rfl
@[simp] theorem transposeBit_true {n : ℕ} (p : Equiv.Perm (Fin n)) :
    transposeBit true p = p.symm := rfl

@[simp] theorem transposeBit_involutive {n : ℕ} (b : Bool) (p : Equiv.Perm (Fin n)) :
    transposeBit b (transposeBit b p) = p := by cases b <;> rfl

 theorem labels_transpose {n : ℕ} (p : Equiv.Perm (Fin n)) : labels p.symm = labels p := by
  rw [← matrixCells_labels, matrixCells_transpose, Multiset.map_map, ← matrixCells_labels p]
  apply Multiset.map_congr rfl
  intro x _
  dsimp
  ring

@[simp] theorem labels_transposeBit {n : ℕ} (b : Bool) (p : Equiv.Perm (Fin n)) :
    labels (transposeBit b p) = labels p := by
  cases b
  · rfl
  · exact labels_transpose p

 theorem OrientedPromotion.bits_disjoint {m : ℕ} (hm : 1 ≤ m)
    {p r : Equiv.Perm (Fin (m + 1))} {q w : Equiv.Perm (Fin (m + 2))}
    (hzero : p 0 = r 0) (hp : OrientedPromotion p q) (hr : OrientedPromotion r w) :
    q ≠ w.symm := by
  intro he
  have hh := hp.low
  rw [he, matrixCells_transpose] at hh
  obtain ⟨z, hz, hez⟩ := Multiset.mem_map.mp hh
  have hez' : z = ((r 0).val + (2 : ℤ), 1) := by
    have hh := congrArg Prod.swap hez
    simpa only [Prod.swap_swap, Prod.swap_prod_mk, hzero] using hh
  exact hr.no_reverse hm (hez' ▸ hz)

/-- The two orientations give disjoint, recoverable copies for each fixed
first-row source cell. -/
theorem promotion_bits_injective {m : ℕ} (hm : 1 ≤ m)
    {p r : Equiv.Perm (Fin (m + 1))} {q w : Equiv.Perm (Fin (m + 2))}
    (hzero : p 0 = r 0) (hp : OrientedPromotion p q) (hr : OrientedPromotion r w)
    (b c : Bool) (he : transposeBit b q = transposeBit c w) : p = r ∧ b = c := by
  cases b <;> cases c
  · change q = w at he
    subst w
    exact ⟨hp.source_unique hm hzero hr, rfl⟩
  · exact (hp.bits_disjoint hm hzero hr he).elim
  · have he' : w = q.symm := he.symm
    exact (hr.bits_disjoint hm hzero.symm hp he').elim
  · have he' : q = w := by
      have hh := congrArg Equiv.symm he
      simpa only [transposeBit_true, Equiv.symm_symm] using hh
    subst w
    exact ⟨hp.source_unique hm hzero hr, rfl⟩

end XRay
