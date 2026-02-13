

theorem interior_closure_interior_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  intro x hx
  have h_closure_subset : (closure (interior A) : Set X) ⊆ closure A :=
    closure_mono (interior_subset : (interior A : Set X) ⊆ A)
  exact (interior_mono h_closure_subset) hx