import XRay.RootedPaths

namespace XRay
open Finset

/-- The ordered cell before adding coordinate offsets. -/
def switchPair {α : Type*} [DecidableEq α] (P : Finset α) (f : α → α) (x : α) : α × α :=
  if x ∈ P then (f x, x) else (x, f x)

namespace PathSupport
variable {α : Type*} [DecidableEq α] {D : Finset α} {f : α → α} {s t : α}

 theorem source_mem (P : PathSupport D f s t) (_hs : s ∉ D.image f) (hsd : s ∈ D) :
    s ∈ P.vertices := by
  have hm : s ∈ P.vertices.val + {t} := by
    rw [← P.balance]
    simp
  rcases Multiset.mem_add.mp hm with hm | hm
  · exact hm
  · have he : s = t := by simpa using hm
    exact False.elim (P.terminal (he ▸ hsd))

 theorem next_mem (P : PathSupport D f s t) (hf : Set.InjOn f D)
    (hs : s ∉ D.image f) {x : α} (hx : x ∈ P.vertices) (hfx : f x ∈ D) :
    f x ∈ P.vertices := by
  have hc := P.count_balance hf hs (P.subset_domain hx)
  have ht : f x ≠ t := fun h => P.terminal (h ▸ hfx)
  simp only [if_pos hx, if_neg ht, add_zero] at hc
  split_ifs at hc with h
  · exact h

 theorem reachable_mem (P : PathSupport D f s t) (hf : Set.InjOn f D)
    (hs : s ∉ D.image f) {x : α}
    (hr : Relation.ReflTransGen (fun a b => a ∈ D ∧ f a = b) s x) (hx : x ∈ D) :
    x ∈ P.vertices := by
  induction hr with
  | refl => exact P.source_mem hs hx
  | @tail a b hr hab ih =>
    rw [← hab.2] at hx ⊢
    exact P.next_mem hf hs (ih hab.1) hx

/-- The column at a switched path vertex identifies its own source edge. -/
theorem switch_column_unique (P : PathSupport D f s t) (hf : Set.InjOn f D)
    (hs : s ∉ D.image f) {x y : α} (hx : x ∈ P.vertices) (hy : y ∈ D)
    (he : (switchPair P.vertices f y).2 = x) : y = x := by
  by_cases hyp : y ∈ P.vertices
  · simpa only [switchPair, if_pos hyp] using he
  · have hfy : f y = x := by simpa only [switchPair, if_neg hyp] using he
    have hc := P.count_balance hf hs hy
    rw [hfy, if_pos hx, if_neg hyp] at hc
    omega

end PathSupport

/-- Equal switched-cell multisets agree on every vertex switched by both. -/
theorem switch_agrees_on_common {α : Type*} [DecidableEq α] {D : Finset α}
    {f g : α → α} {s t : α} (P : PathSupport D f s t) (Q : PathSupport D g s t)
    (hg : Set.InjOn g D) (hs : s ∉ D.image g)
    (heq : D.val.map (switchPair P.vertices f) = D.val.map (switchPair Q.vertices g))
    {x : α} (hxp : x ∈ P.vertices) (hxq : x ∈ Q.vertices) : f x = g x := by
  have hm : switchPair P.vertices f x ∈ D.val.map (switchPair Q.vertices g) := by
    rw [← heq]
    exact Multiset.mem_map.mpr ⟨x, P.subset_domain hxp, rfl⟩
  obtain ⟨y, hy, he⟩ := Multiset.mem_map.mp hm
  have hcol : (switchPair Q.vertices g y).2 = x := by
    simpa only [switchPair, if_pos hxp] using congrArg Prod.snd he
  have hyx := Q.switch_column_unique hg hs hxq hy hcol
  subst y
  simpa only [switchPair, if_pos hxp, if_pos hxq] using (congrArg Prod.fst he).symm

/-- The rooted condition makes the path switch invertible; detached cycles
would otherwise allow an undetectable extra reversal. -/
theorem rooted_switch_injective {α : Type*} [DecidableEq α] {D : Finset α}
    {f g : α → α} {s t : α} (P : RootedPath D f s t) (Q : RootedPath D g s t)
    (hf : Set.InjOn f D) (hg : Set.InjOn g D)
    (hsf : s ∉ D.image f) (hsg : s ∉ D.image g)
    (heq : D.val.map (switchPair P.vertices f) = D.val.map (switchPair Q.vertices g)) :
    P.vertices = Q.vertices ∧ ∀ x ∈ D, f x = g x := by
  have sub {f g : α → α} (P : RootedPath D f s t) (Q : RootedPath D g s t)
      (hf : Set.InjOn f D) (hg : Set.InjOn g D)
      (hsf : s ∉ D.image f) (hsg : s ∉ D.image g)
      (heq : D.val.map (switchPair P.vertices f) = D.val.map (switchPair Q.vertices g)) :
      P.vertices ⊆ Q.vertices := by
    intro x hx
    have hr := P.reachable x hx
    have aux {x : α} (hr : Relation.ReflTransGen (fun a b => a ∈ D ∧ f a = b) s x) :
        x ∈ D → x ∈ Q.vertices := by
      induction hr with
      | refl => exact Q.toPathSupport.source_mem hsg
      | @tail a b hr hab ih =>
        intro hb
        have ha := ih hab.1
        have hap := P.toPathSupport.reachable_mem hf hsf hr hab.1
        have he := switch_agrees_on_common P.toPathSupport Q.toPathSupport hg hsg heq hap ha
        have hgb : g a = b := he.symm.trans hab.2
        rw [← hgb] at hb ⊢
        exact Q.toPathSupport.next_mem hg hsg ha hb
    exact aux hr (P.subset_domain hx)
  have hPQ : P.vertices = Q.vertices :=
    Subset.antisymm (sub P Q hf hg hsf hsg heq) (sub Q P hg hf hsg hsf heq.symm)
  refine ⟨hPQ, fun x hx => ?_⟩
  by_cases hxp : x ∈ P.vertices
  · exact switch_agrees_on_common P.toPathSupport Q.toPathSupport hg hsg heq hxp (hPQ ▸ hxp)
  · have hxq : x ∉ Q.vertices := hPQ ▸ hxp
    have hm : switchPair P.vertices f x ∈ D.val.map (switchPair Q.vertices g) := by
      rw [← heq]
      exact Multiset.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, he⟩ := Multiset.mem_map.mp hm
    by_cases hyp : y ∈ Q.vertices
    · have hrow : g y = x := by
        simpa only [switchPair, if_pos hyp, if_neg hxp] using congrArg Prod.fst he
      have hmem := Q.toPathSupport.next_mem hg hsg hyp (hrow ▸ hx)
      exact False.elim (hxq (hrow ▸ hmem))
    · have hyx : y = x := by
        simpa only [switchPair, if_neg hyp, if_neg hxp] using congrArg Prod.fst he
      subst y
      simpa only [switchPair, if_neg hxp, if_neg hxq] using (congrArg Prod.snd he).symm

end XRay
