import XRay.Paths

namespace XRay
open Finset

/-- A source-to-sink support whose vertices are all reached before leaving
the partial injection's domain. This excludes detached cycles. -/
structure RootedPath {α : Type*} [DecidableEq α]
    (D : Finset α) (f : α → α) (s t : α) extends PathSupport D f s t where
  reachable : ∀ x ∈ vertices,
    Relation.ReflTransGen (fun a b => a ∈ D ∧ f a = b) s x

/-- A source of a finite partial injection always reaches a sink. -/
theorem exists_rootedPath {α : Type*} [DecidableEq α]
    (D : Finset α) (f : α → α) (hf : Set.InjOn f D)
    (s : α) (hs : s ∉ D.image f) : ∃ t, Nonempty (RootedPath D f s t) := by
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
      refine ⟨t, ⟨⟨⟨insert s P.vertices, ?_, htd, ?_⟩, ?_⟩⟩⟩
      · intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact hsd
        · exact mem_of_mem_erase (P.subset_domain ha)
      · rw [Finset.insert_val_of_notMem hsp, Multiset.map_cons]
        simpa only [← Multiset.singleton_add, add_assoc, add_left_comm, add_comm]
          using congrArg (fun M : Multiset α => M + {s}) P.balance
      · intro x hx
        rcases mem_insert.mp hx with rfl | hx
        · exact Relation.ReflTransGen.refl
        · have hp := P.reachable x hx
          have hp' : Relation.ReflTransGen (fun a b => a ∈ D ∧ f a = b) (f s) x := by
            exact Relation.ReflTransGen.mono (fun a b h => ⟨mem_of_mem_erase h.1, h.2⟩) _ _ hp
          exact hp'.head ⟨hsd, rfl⟩
    · exact ⟨s, ⟨⟨⟨∅, empty_subset D, hsd, by simp⟩,
        by intro x hx; simp at hx⟩⟩⟩

end XRay
