

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h₁ : interior A ⊆ A := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono h₁
  simpa [hA.closure_eq] using h₂