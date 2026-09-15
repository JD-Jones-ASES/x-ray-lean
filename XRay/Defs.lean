import Mathlib

/-! Definitions use zero-based indices and one-based antidiagonal labels. -/
namespace XRay

/-- Labels in increasing rank order. Index `i` denotes rank `i + 1`. -/
abbrev Profile (n : ℕ) := Fin n → ℤ

/-- Density slack after the first `k` labels. -/
def slack {n : ℕ} (L : Profile n) (k : ℕ) : ℤ :=
  (∑ i : Fin n with i.val < k, L i) - (k : ℤ) ^ 2

/-- Difference from the odd staircase at the same rank. -/
def deviation {n : ℕ} (L : Profile n) (i : Fin n) : ℤ :=
  L i - (2 * (i.val : ℤ) + 1)

/-- The usual necessary conditions for a binary permutation X-ray. -/
def Admissible {n : ℕ} (L : Profile n) : Prop :=
  StrictMono L ∧ (∀ i, 1 ≤ L i ∧ L i ≤ 2 * (n : ℤ) - 1) ∧
    (∀ k ≤ n, 0 ≤ slack L k) ∧ slack L n = 0

/-- Assign each ranked label to a distinct row and a distinct column.
The one-based cell `(r + 1, c + 1)` has label `r + c + 1`. -/
def Realizable {n : ℕ} (L : Profile n) : Prop :=
  ∃ r c : Equiv.Perm (Fin n), ∀ i, L i = (r i).val + (c i).val + (1 : ℤ)

/-- Literal label multiset of a permutation matrix. -/
def labels {n : ℕ} (p : Equiv.Perm (Fin n)) : Multiset ℤ :=
  Finset.univ.val.map (fun i : Fin n => (i.val : ℤ) + (p i).val + 1)

/-- Number of permutation matrices with the prescribed label multiset. -/
noncomputable def fiberCount {n : ℕ} (L : Profile n) : ℕ := by
  classical
  exact Fintype.card {p : Equiv.Perm (Fin n) //
    labels p = Finset.univ.val.map L}

/-- Add the two extension labels; their slot order is immaterial. -/
def extend {n : ℕ} (L : Profile n) : Profile (n + 2) :=
  Fin.addCases (fun i => L i + 2) ![3, 2 * (n : ℤ) + 1]

/-- Number of ranks with positive deviation. -/
noncomputable def positiveCount {n : ℕ} (L : Profile n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => 0 < deviation L i)).card

/-- Number of ranks with negative deviation. -/
noncomputable def negativeCount {n : ℕ} (L : Profile n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => deviation L i < 0)).card

end XRay
