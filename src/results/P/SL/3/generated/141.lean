

theorem interior_closure_interior_closure_subset_interior_closure {X : Type*}
    [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) ⊆
      interior (closure (A : Set X)) := by
  simpa [closure_closure] using
    interior_closure_interior_subset_interior_closure
      (A := closure (A : Set X))