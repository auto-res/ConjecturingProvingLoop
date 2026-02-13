

theorem interior_subset_closure_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (A : Set X) := by
  intro x hx
  exact subset_closure (interior_subset hx)