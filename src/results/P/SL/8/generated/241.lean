

theorem interior_subset_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior A) := by
  intro x hx
  exact subset_closure hx