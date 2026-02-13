

theorem interior_closure_interior_subset {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ interior (closure A) := by
  exact interior_mono (closure_mono (interior_subset : (interior A : Set X) ⊆ A))