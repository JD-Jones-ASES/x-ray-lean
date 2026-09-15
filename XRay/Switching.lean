import XRay.IntegerCells
import XRay.Paths

namespace XRay
open Finset

/-- Row coordinate after switching a path of shifted permutation cells. -/
def switchedRow (P : Finset ℤ) (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  if x ∈ P then f x + 2 else x + 2

/-- Column coordinate after the same switch. -/
def switchedCol (P : Finset ℤ) (f : ℤ → ℤ) (x : ℤ) : ℤ :=
  if x ∈ P then x + 3 else f x + 3

 theorem switched_label (P : Finset ℤ) (f : ℤ → ℤ) (x : ℤ) :
    switchedRow P f x + switchedCol P f x - 1 = x + f x + 4 := by
  simp only [switchedRow, switchedCol]
  split_ifs <;> ring

/-- The switch changes exactly the two endpoint row incidences. -/
theorem PathSupport.row_margin {D : Finset ℤ} {f : ℤ → ℤ} {s t : ℤ}
    (P : PathSupport D f s t) :
    D.val.map (switchedRow P.vertices f) + {s + 2} =
      D.val.map (fun x => x + 2) + {t + 2} := by
  have hb := congrArg (Multiset.map (fun x : ℤ => x + 2)) P.balance
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def] at hb
  have hd := map_ite_of_subset D P.vertices P.subset_domain
    (fun x : ℤ => x + 2) (fun x : ℤ => x + 2)
  simp only [ite_self] at hd
  unfold switchedRow
  rw [map_ite_of_subset D P.vertices P.subset_domain, hd]
  calc
    _ = (P.vertices.val.map (fun x => f x + 2) + {s + 2}) +
        (SDiff.sdiff D P.vertices).val.map (fun x => x + 2) := by ac_rfl
    _ = _ := by rw [hb]; ac_rfl

/-- The switch changes exactly the two endpoint column incidences. -/
theorem PathSupport.col_margin {D : Finset ℤ} {f : ℤ → ℤ} {s t : ℤ}
    (P : PathSupport D f s t) :
    D.val.map (switchedCol P.vertices f) + {t + 3} =
      D.val.map (fun x => f x + 3) + {s + 3} := by
  have hb := congrArg (Multiset.map (fun x : ℤ => x + 3)) P.balance
  simp only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def] at hb
  have hd := map_ite_of_subset D P.vertices P.subset_domain
    (fun x : ℤ => f x + 3) (fun x : ℤ => f x + 3)
  simp only [ite_self] at hd
  unfold switchedCol
  rw [map_ite_of_subset D P.vertices P.subset_domain, hd]
  calc
    _ = (P.vertices.val.map (fun x => x + 3) + {t + 3}) +
        (SDiff.sdiff D P.vertices).val.map (fun x => f x + 3) := by ac_rfl
    _ = _ := by rw [← hb]; ac_rfl

end XRay
