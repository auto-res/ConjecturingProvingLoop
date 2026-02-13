

theorem interior_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (A : Set X) ⊆ closure (interior (A : Set X)) := by
  intro x hx
  exact subset_closure hx