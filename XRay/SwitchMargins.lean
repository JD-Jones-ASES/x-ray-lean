import XRay.SwitchInverse
import XRay.Switching

namespace XRay

 theorem PathSupport.switch_fst_margin {D : Finset ℤ} {f : ℤ → ℤ} {s t : ℤ}
    (P : PathSupport D f s t) :
    D.val.map (fun x => (switchPair P.vertices f x).1) + {s} = D.val + {t} := by
  have hh := congrArg (Multiset.map (fun z : ℤ => z - 2)) P.row_margin
  have he (x : ℤ) : switchedRow P.vertices f x - 2 = (switchPair P.vertices f x).1 := by
    simp only [switchedRow, switchPair]
    split_ifs <;> simp
  simpa only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def, he, add_sub_cancel_right, Multiset.map_id'] using hh

 theorem PathSupport.switch_snd_margin {D : Finset ℤ} {f : ℤ → ℤ} {s t : ℤ}
    (P : PathSupport D f s t) :
    D.val.map (fun x => (switchPair P.vertices f x).2) + {t} = D.val.map f + {s} := by
  have hh := congrArg (Multiset.map (fun z : ℤ => z - 3)) P.col_margin
  have he (x : ℤ) : switchedCol P.vertices f x - 3 = (switchPair P.vertices f x).2 := by
    simp only [switchedCol, switchPair]
    split_ifs <;> simp
  simpa only [Multiset.map_add, Multiset.map_singleton, Multiset.map_map,
    Function.comp_def, he, add_sub_cancel_right] using hh

end XRay
