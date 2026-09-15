import Mathlib

/-! A finite degree-two multigraph can be oriented as a permutation.
Edges are indexed, so loops and parallel edges are retained. -/
namespace XRay
open Finset

/-- The number of incidences of the indexed edge `(u e, v e)` at `x`. -/
def incidence {n : ℕ} (u v : Fin n → Fin n) (e x : Fin n) : ℕ :=
  (if u e = x then 1 else 0) + (if v e = x then 1 else 0)

/-- Two incidences at every vertex, counting a loop twice. -/
def DegreeTwo {n : ℕ} (u v : Fin n → Fin n) : Prop :=
  ∀ x, ∑ e, incidence u v e x = 2

theorem degreeTwo_hall {n : ℕ} {u v : Fin n → Fin n}
    (h : DegreeTwo u v) (s : Finset (Fin n)) :
    s.card ≤ (s.biUnion (fun e => {u e, v e})).card := by
  classical
  let t := s.biUnion (fun e => {u e, v e})
  have edge_sum (e : Fin n) (he : e ∈ s) :
      ∑ x ∈ t, incidence u v e x = 2 := by
    have hu : u e ∈ t := mem_biUnion.mpr ⟨e, he, by simp⟩
    have hv : v e ∈ t := mem_biUnion.mpr ⟨e, he, by simp⟩
    simp [incidence, sum_add_distrib, hu, hv]
  have vertex_sum (x : Fin n) : ∑ e ∈ s, incidence u v e x ≤ 2 := by
    rw [← h x]
    exact sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hc : 2 * s.card ≤ 2 * t.card := calc
    2 * s.card = ∑ e ∈ s, ∑ x ∈ t, incidence u v e x := by
      simp only [sum_congr rfl edge_sum, sum_const, smul_eq_mul]
      omega
    _ = ∑ x ∈ t, ∑ e ∈ s, incidence u v e x := sum_comm
    _ ≤ ∑ x ∈ t, 2 := sum_le_sum (fun x _ => vertex_sum x)
    _ = 2 * t.card := by simp [Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left hc (by decide)

/-- Every indexed degree-two multigraph admits an orientation with one
incoming and one outgoing edge at each vertex. -/
theorem orient_degreeTwo {n : ℕ} {u v : Fin n → Fin n}
    (h : DegreeTwo u v) :
    ∃ a b : Equiv.Perm (Fin n), ∀ e,
      (a e = u e ∧ b e = v e) ∨ (a e = v e ∧ b e = u e) := by
  classical
  obtain ⟨f, hf, hmem⟩ :=
    (all_card_le_biUnion_card_iff_existsInjective' (fun e => {u e, v e})).mp
      (degreeTwo_hall h)
  have hfb : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩
  let a : Equiv.Perm (Fin n) := Equiv.ofBijective f hfb
  let g : Fin n → Fin n := fun e => if f e = u e then v e else u e
  have choices (e : Fin n) :
      (f e = u e ∧ g e = v e) ∨ (f e = v e ∧ g e = u e) := by
    have hm : f e = u e ∨ f e = v e := by simpa using hmem e
    by_cases he : f e = u e
    · exact Or.inl ⟨he, by simp [g, he]⟩
    · exact Or.inr ⟨hm.resolve_left he, by simp [g, he]⟩
  have balance (e x : Fin n) :
      (if f e = x then 1 else 0) + (if g e = x then 1 else 0) =
        incidence u v e x := by
    rcases choices e with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
      simp [h₁, h₂, incidence, Nat.add_comm]
  have gs : Function.Surjective g := by
    intro x
    by_contra hn
    have hg : ∀ e, g e ≠ x := by simpa using hn
    have hh := h x
    have hsum : ∑ e, (if f e = x then 1 else 0) = 1 := by
      simpa [a] using (Equiv.sum_comp a (fun y => if y = x then (1 : ℕ) else 0))
    simp_rw [← balance, if_neg (hg _), Nat.add_zero] at hh
    omega
  let b : Equiv.Perm (Fin n) := Equiv.ofBijective g
    ((Fintype.bijective_iff_surjective_and_card g).mpr ⟨gs, rfl⟩)
  exact ⟨a, b, choices⟩

end XRay
