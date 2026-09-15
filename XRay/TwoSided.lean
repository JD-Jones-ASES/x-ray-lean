import XRay.EndpointReduction

namespace XRay

/-- Every admissible binary profile within two of the odd staircase is
realizable, at every finite order. -/
theorem two_sided {n : ℕ} (_hn : 1 ≤ n) (L : Profile n) (hL : Admissible L)
    (hd : ∀ i, -2 ≤ deviation L i ∧ deviation L i ≤ 2) : Realizable L := by
  have hall : ∀ m : ℕ, ∀ K : Profile m, Admissible K →
      (∀ i, -2 ≤ deviation K i ∧ deviation K i ≤ 2) → Realizable K := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro K hK hD
      by_cases hm : 1 ≤ m
      · apply endpoint_reduction hm (D := fun d => -2 ≤ d ∧ d ≤ 2)
          (fun d h₁ h₂ => ⟨h₁, h₂⟩) (fun d h => by constructor <;> omega)
          (fun r hr A hA hFit => ih r hr A hA hFit) K hK hD
        · have hh := (hD ⟨0, hm⟩).2
          simp only [deviation, Nat.cast_zero, mul_zero, zero_add] at hh
          omega
        · have hh := (hD ⟨m - 1, by omega⟩).1
          simp only [deviation] at hh
          omega
      · have hm0 : m = 0 := by omega
        subst m
        exact ⟨Equiv.refl _, Equiv.refl _, fun i => Fin.elim0 i⟩
  exact hall n L hL hd

/-- A least-order counterexample must leave the small-endpoint region. -/
theorem least_counterexample {n : ℕ} (hn : 1 ≤ n) (L : Profile n)
    (hL : Admissible L) (hno : ¬ Realizable L)
    (hsmall : ∀ m < n, ∀ K : Profile m, Admissible K → Realizable K) :
    3 ≤ deviation L ⟨0, hn⟩ ∨ deviation L ⟨n - 1, by omega⟩ ≤ -3 := by
  by_contra hh
  push Not at hh
  apply hno
  apply endpoint_reduction hn (D := fun _ => True) (fun _ _ _ => True.intro)
    (fun _ _ => True.intro) (fun m hm K hK _ => hsmall m hm K hK) L hL
    (fun _ => True.intro)
  · have h := hh.1
    simp only [deviation, Nat.cast_zero, mul_zero, zero_add] at h
    omega
  · have h := hh.2
    simp only [deviation] at h
    omega

end XRay
