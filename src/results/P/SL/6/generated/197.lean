

theorem closure_union_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : (A : Set X) ⊆ C) (hB : (B : Set X) ⊆ C) :
    closure (A ∪ B : Set X) ⊆ closure C := by
  exact closure_mono (by
    intro x hx
    cases hx with
    | inl hAx => exact hA hAx
    | inr hBx => exact hB hBx)