

theorem interior_closure_interior_eq_interior_of_closed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (closure (interior A)) = interior A := by
  apply subset_antisymm
  · -- `interior (closure (interior A)) ⊆ interior A`
    have h_closure_subset : closure (interior A) ⊆ A := by
      have h_int_subset : interior A ⊆ A := interior_subset
      have h' : closure (interior A) ⊆ closure A := closure_mono h_int_subset
      simpa [hA.closure_eq] using h'
    exact interior_mono h_closure_subset
  · -- `interior A ⊆ interior (closure (interior A))`
    have h_subset : interior A ⊆ closure (interior A) := by
      intro x hx
      exact subset_closure hx
    have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono h_subset
    simpa [interior_interior] using h'