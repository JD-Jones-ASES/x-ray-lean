/- Target statements. The placeholders in this file are intentional.
Solution.lean must establish exactly these statements before release. -/
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

/-- Every admissible binary profile with all rank deviations in [-2, 2]. -/
theorem two_sided {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -2 ≤ deviation L i ∧ deviation L i ≤ 2) : Realizable L := by sorry

/-- The lower one-sided family. -/
theorem one_sided_lower {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : Realizable L := by sorry

/-- Its reflected family. -/
theorem one_sided_upper {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, deviation L i ≤ 1) : Realizable L := by sorry

/-- The lower family has at least two to the number of positive deviations. -/
theorem one_sided_lower_count {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -1 ≤ deviation L i) : 2 ^ positiveCount L ≤ fiberCount L := by sorry

/-- The upper family has the reflected counting bound. -/
theorem one_sided_upper_count {n : ℕ} (hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, deviation L i ≤ 1) : 2 ^ negativeCount L ≤ fiberCount L := by sorry

/-- Q extension for every supplied realization, including repeated labels. -/
theorem ordinary_extension {n : ℕ} (hn : 1 ≤ n) {L : Profile n}
    (h : Realizable L) : Realizable (extend L) := by sorry

/-- The Q extension is injective on each interior source fiber. -/
theorem extension_count {n : ℕ} (hn : 1 ≤ n) (L : Profile n)
    (hL : ∀ i, 2 ≤ L i ∧ L i ≤ 2 * (n : ℤ) - 2) :
    fiberCount L ≤ fiberCount (extend L) := by sorry

/-- Endpoint restriction on a least-order counterexample. -/
theorem least_counterexample {n : ℕ} (hn : 1 ≤ n) (L : Profile n)
    (hL : Admissible L) (hno : ¬ Realizable L)
    (hsmall : ∀ m < n, ∀ K : Profile m, Admissible K → Realizable K) :
    3 ≤ deviation L ⟨0, hn⟩ ∨ deviation L ⟨n - 1, by omega⟩ ≤ -3 := by sorry

end XRay
