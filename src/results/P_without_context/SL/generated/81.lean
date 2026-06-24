

theorem closure_subset_of_subset_closed
    {α : Type*} [TopologicalSpace α] {s t : Set α}
    (h₁ : s ⊆ t) (h₂ : IsClosed t) : closure s ⊆ t := by
  exact closure_minimal h₁ h₂