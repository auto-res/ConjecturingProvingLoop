

theorem interior_closure_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure A) ⊆ closure A := by
  intro x hx
  exact interior_subset hx