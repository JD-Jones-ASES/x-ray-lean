import XRay.Defs
import XRay.Orientation

namespace XRay
open Finset

/-- Relabeling the cells changes their index order, but not realizability. -/
theorem Realizable.reindex {n : ℕ} {L : Profile n} (h : Realizable L)
    (e : Equiv.Perm (Fin n)) : Realizable (L ∘ e) := by
  obtain ⟨r, c, hrc⟩ := h
  exact ⟨e.trans r, e.trans c, fun i => hrc (e i)⟩

/-- A degree-two representation can be oriented without changing any label. -/
theorem realizable_of_degreeTwo {n : ℕ} {L : Profile n} {u v : Fin n → Fin n}
    (h : DegreeTwo u v) (hL : ∀ i, L i = (u i).val + (v i).val + (1 : ℤ)) :
    Realizable L := by
  obtain ⟨a, b, hab⟩ := orient_degreeTwo h
  refine ⟨a, b, fun i => ?_⟩
  rcases hab i with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa [ha, hb] using hL i
  · rw [ha, hb, hL i]
    ring

/-- Every realization in ranked-cell form is an actual permutation matrix. -/
theorem Realizable.matrix {n : ℕ} {L : Profile n} (h : Realizable L) :
    ∃ p : Equiv.Perm (Fin n), labels p = univ.val.map L := by
  obtain ⟨r, c, hrc⟩ := h
  refine ⟨r.symm.trans c, ?_⟩
  unfold labels
  conv_lhs => rw [← Multiset.map_univ_val_equiv r, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simpa [Function.comp_def] using (hrc i).symm

/-- The matrix associated to specified row and column assignments. -/
theorem matrix_of_assignments {n : ℕ} {L : Profile n}
    (r c : Equiv.Perm (Fin n)) (hrc : ∀ i, L i = (r i).val + (c i).val + (1 : ℤ)) :
    labels (r.symm.trans c) = univ.val.map L := by
  unfold labels
  conv_lhs => rw [← Multiset.map_univ_val_equiv r, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i _
  simpa [Function.comp_def] using (hrc i).symm

/-- A realization with a zero endpoint at its first-ranked cell can be
transposed to put that cell in the first row. -/
theorem first_row_of_zero_endpoint {m : ℕ} {K : Profile (m + 1)}
    (r c : Equiv.Perm (Fin (m + 1)))
    (hrc : ∀ i, K i = (r i).val + (c i).val + (1 : ℤ))
    (hz : r 0 = 0 ∨ c 0 = 0) :
    ∃ p : Equiv.Perm (Fin (m + 1)), labels p = univ.val.map K ∧
      (p 0).val + (1 : ℤ) = K 0 := by
  have aux (a b : Equiv.Perm (Fin (m + 1)))
      (hab : ∀ i, K i = (a i).val + (b i).val + (1 : ℤ)) (ha : a 0 = 0) :
      ∃ p : Equiv.Perm (Fin (m + 1)), labels p = univ.val.map K ∧
        (p 0).val + (1 : ℤ) = K 0 := by
    refine ⟨a.symm.trans b, matrix_of_assignments a b hab, ?_⟩
    have hai : a.symm 0 = 0 := a.symm_apply_eq.mpr ha.symm
    simpa only [Equiv.trans_apply, hai, ha, Fin.val_zero, Nat.cast_zero, zero_add]
      using (hab 0).symm
  rcases hz with hz | hz
  · exact aux r c hrc hz
  · exact aux c r (fun i => by rw [hrc i]; ring) hz

 theorem first_row_of_small_label {m : ℕ} {K : Profile (m + 1)}
    (h : Realizable K) (hk : K 0 ≤ 2) :
    ∃ p : Equiv.Perm (Fin (m + 1)), labels p = univ.val.map K ∧
      (p 0).val + (1 : ℤ) = K 0 := by
  obtain ⟨r, c, hrc⟩ := h
  apply first_row_of_zero_endpoint r c hrc
  have hh := hrc 0
  by_cases hr : (r 0).val = 0
  · exact Or.inl (Fin.ext hr)
  · exact Or.inr (Fin.ext (show (c 0).val = 0 by omega))

/-- Reindex two finite functions with the same multiset of values. -/
theorem equiv_of_map_univ_eq {n : ℕ} {f g : Fin n → ℤ}
    (h : univ.val.map f = univ.val.map g) :
    ∃ e : Equiv.Perm (Fin n), ∀ i, g (e i) = f i := by
  classical
  have hc (z : ℤ) : Fintype.card {i // f i = z} = Fintype.card {i // g i = z} := by
    have hh := congrArg (Multiset.count z) h
    simp only [Multiset.count_map] at hh
    simpa only [Fintype.card_subtype, Finset.card_def, Finset.filter_val, eq_comm] using hh
  let e (z : ℤ) := Fintype.equivOfCardEq (hc z)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

theorem Realizable.of_multiset {n : ℕ} {A B : Profile n} (h : Realizable A)
    (heq : univ.val.map B = univ.val.map A) : Realizable B := by
  obtain ⟨e, he⟩ := equiv_of_map_univ_eq heq
  have hfun : B = A ∘ e := funext (fun i => (he i).symm)
  rw [hfun]
  exact h.reindex e

/-- Ranked-cell realization and the literal matrix definition are equivalent,
including profiles with repeated labels. -/
theorem realizable_iff_matrix {n : ℕ} {L : Profile n} :
    Realizable L ↔ ∃ p : Equiv.Perm (Fin n), labels p = univ.val.map L := by
  refine ⟨Realizable.matrix, ?_⟩
  rintro ⟨p, hp⟩
  obtain ⟨e, he⟩ := equiv_of_map_univ_eq hp.symm
  exact ⟨e, e.trans p, fun i => (he i).symm⟩

@[simp] theorem slack_zero {n : ℕ} (L : Profile n) : slack L 0 = 0 := by
  simp [slack]

 theorem slack_order {n : ℕ} (L : Profile n) :
    slack L n = (∑ i, L i) - (n : ℤ) ^ 2 := by
  simp [slack]

/-- Consecutive slacks differ by the rank deviation. -/
theorem slack_succ {n k : ℕ} (L : Profile n) (hk : k < n) :
    slack L (k + 1) = slack L k + deviation L ⟨k, hk⟩ := by
  have hset : (univ.filter fun i : Fin n => i.val < k + 1) =
      insert ⟨k, hk⟩ (univ.filter fun i : Fin n => i.val < k) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert]
    constructor
    · intro hi
      by_cases h : i.val = k
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (by omega)
    · rintro (rfl | hi) <;> simp_all; omega
  have hn : (⟨k, hk⟩ : Fin n) ∉ univ.filter (fun i : Fin n => i.val < k) := by simp
  simp only [slack, deviation, hset, sum_insert hn, Nat.cast_add, Nat.cast_one]
  ring

 theorem admissible_total {n : ℕ} {L : Profile n} (h : Admissible L) :
    ∑ i, L i = (n : ℤ) ^ 2 := by
  have ht := h.2.2.2
  rw [slack_order] at ht
  linarith

end XRay
