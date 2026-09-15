import Mathlib

/-! Finite paths of a partial injection, recorded by their margin identity. -/
namespace XRay
open Finset

/-- A support with a source-to-sink margin identity. Isolated paths and
disjoint cycles are permitted; the margin arguments need only the identity. -/
structure PathSupport {α : Type*} [DecidableEq α]
    (D : Finset α) (f : α → α) (s t : α) where
  vertices : Finset α
  subset_domain : vertices ⊆ D
  terminal : t ∉ D
  balance : vertices.val.map f + {s} = vertices.val + {t}

/-- A source of a finite partial injection always reaches a sink. -/
theorem exists_pathSupport {α : Type*} [DecidableEq α]
    (D : Finset α) (f : α → α) (hf : Set.InjOn f D)
    (s : α) (hs : s ∉ D.image f) : ∃ t, Nonempty (PathSupport D f s t) := by
  induction D using Finset.strongInductionOn generalizing s with
  | _ D ih =>
    by_cases hsd : s ∈ D
    · have hf' : Set.InjOn f (D.erase s) := hf.mono (erase_subset s D)
      have hs' : f s ∉ (D.erase s).image f := by
        intro hh
        obtain ⟨a, ha, he⟩ := mem_image.mp hh
        have heq := hf (mem_of_mem_erase ha) hsd he
        exact (ne_of_mem_erase ha) heq
      obtain ⟨t, ⟨P⟩⟩ := ih (D.erase s) (erase_ssubset hsd) hf' (f s) hs'
      have hsp : s ∉ P.vertices := by
        intro h; exact (Finset.notMem_erase s D) (P.subset_domain h)
      have htd : t ∉ D := by
        intro ht
        have hts : t = s := by
          by_contra hne
          exact P.terminal (mem_erase.mpr ⟨hne, ht⟩)
        have hm : s ∈ P.vertices.val.map f + {f s} := by
          rw [P.balance]
          simp [hts]
        rcases Multiset.mem_add.mp hm with hm | hm
        · obtain ⟨a, ha, he⟩ := Multiset.mem_map.mp hm
          apply hs
          exact mem_image.mpr ⟨a, mem_of_mem_erase (P.subset_domain ha), he⟩
        · have he : s = f s := by simpa using hm
          exact hs (mem_image.mpr ⟨s, hsd, he.symm⟩)
      refine ⟨t, ⟨⟨insert s P.vertices, ?_, htd, ?_⟩⟩⟩
      · intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact hsd
        · exact mem_of_mem_erase (P.subset_domain ha)
      · rw [Finset.insert_val_of_notMem hsp, Multiset.map_cons]
        simpa only [← Multiset.singleton_add, add_assoc, add_left_comm, add_comm]
          using congrArg (fun M : Multiset α => M + {s}) P.balance
    · exact ⟨s, ⟨⟨∅, empty_subset D, hsd, by simp⟩⟩⟩

namespace PathSupport
variable {α : Type*} [DecidableEq α] {D : Finset α} {f : α → α} {s t : α}

/-- A different source cannot occur in this path or be its terminal vertex. -/
theorem excludes_source (P : PathSupport D f s t) {z : α}
    (hz : z ∉ D.image f) (hne : z ≠ s) : z ∉ P.vertices ∧ z ≠ t := by
  have hm : z ∉ P.vertices.val.map f := by
    intro h
    obtain ⟨a, ha, he⟩ := Multiset.mem_map.mp h
    exact hz (mem_image.mpr ⟨a, P.subset_domain ha, he⟩)
  have hh := congrArg (Multiset.count z) P.balance
  have hzero := Multiset.count_eq_zero.mpr hm
  simp only [Multiset.count_add, hzero, Multiset.count_singleton, if_neg hne,
    Nat.zero_add] at hh
  constructor
  · apply Multiset.count_eq_zero.mp
    omega
  · intro he
    subst z
    simp at hh

/-- Incoming edges along a path are exactly its internal incidences plus
its one terminal incidence. -/
theorem count_balance (P : PathSupport D f s t) (hf : Set.InjOn f D)
    (hs : s ∉ D.image f) {e : α} (he : e ∈ D) :
    (if f e ∈ P.vertices then 1 else 0) + (if f e = t then 1 else 0) =
      (if e ∈ P.vertices then 1 else 0 : ℕ) := by
  have hfs : f e ≠ s := by
    intro h
    exact hs (mem_image.mpr ⟨e, he, h⟩)
  have him : f e ∈ P.vertices.image f ↔ e ∈ P.vertices := by
    constructor
    · rintro h
      obtain ⟨a, ha, hae⟩ := mem_image.mp h
      have h := hf (P.subset_domain ha) he hae
      simpa [h] using ha
    · exact fun h => mem_image.mpr ⟨e, h, rfl⟩
  have hh := congrArg (Multiset.count (f e)) P.balance
  rw [← image_val_of_injOn (hf.mono P.subset_domain)] at hh
  simpa only [Multiset.count_add, Multiset.count_eq_of_nodup (P.vertices.image f).nodup,
    Multiset.count_eq_of_nodup P.vertices.nodup, mem_val, him,
    Multiset.count_singleton, if_neg hfs, Nat.add_zero] using hh.symm

/-- Distinct sources of a partial injection have distinct terminal vertices. -/
theorem terminal_ne (P : PathSupport D f s t) {s' t' : α}
    (Q : PathSupport D f s' t') (hf : Set.InjOn f D)
    (hs : s ∉ D.image f) (hs' : s' ∉ D.image f) (hne : s' ≠ s) : t' ≠ t := by
  intro ht
  subst t'
  have hsp := (P.excludes_source hs' hne).1
  have htp : t ∉ P.vertices := fun h => P.terminal (P.subset_domain h)
  have hst : s' ≠ t := (P.excludes_source hs' hne).2
  have htq : t ∉ Q.vertices := fun h => Q.terminal (Q.subset_domain h)
  let w : α → ℕ := fun x => if x ∈ P.vertices then 1 else 0
  have hw := congrArg (fun M : Multiset α => (M.map w).sum) Q.balance
  have hw' : (∑ e ∈ Q.vertices, w (f e)) = ∑ e ∈ Q.vertices, w e := by
    simpa only [Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, Multiset.map_map, w, if_neg hsp, if_neg htp,
      Nat.add_zero, ← Finset.sum_eq_multiset_sum, Function.comp_def] using hw
  have hc : (∑ e ∈ Q.vertices, if f e = t then 1 else 0) = 1 := by
    have hh := congrArg (Multiset.count t) Q.balance
    simp only [Multiset.count_add, Multiset.count_singleton, if_neg hst.symm,
      Multiset.count_eq_zero.mpr htq, Nat.add_zero, Nat.zero_add] at hh
    simpa only [Multiset.count_map, ← filter_val, ← card_def, card_filter, eq_comm, ite_true, eq_self] using hh
  have htotal := Finset.sum_congr rfl (fun e he =>
    P.count_balance hf hs (Q.subset_domain he))
  rw [sum_add_distrib, hc] at htotal
  change (∑ e ∈ Q.vertices, w (f e)) + 1 = ∑ e ∈ Q.vertices, w e at htotal
  omega

end PathSupport
end XRay
