

theorem closure_interior_subset_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  -- The interior of `A` is contained in `A`.
  have hsubset : (interior A : Set X) ⊆ A := interior_subset
  -- Since `A` is closed, its closure is itself. Apply `closure_minimal`.
  exact closure_minimal hsubset hA