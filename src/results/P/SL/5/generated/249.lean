

theorem interior_inter_compl_eq_empty {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ∩ interior ((A : Set X)ᶜ) = (∅ : Set X) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hIntA, hIntAc⟩
    have hA : x ∈ (A : Set X) := interior_subset hIntA
    have hAc : x ∈ ((A : Set X)ᶜ) := interior_subset hIntAc
    have hContr : False := hAc hA
    exact False.elim hContr
  · intro hx
    cases hx