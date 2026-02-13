

theorem interior_closure_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact subset_closure hx