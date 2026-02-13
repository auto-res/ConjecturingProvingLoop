

theorem interior_closure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  simpa using
    (subset_closure :
      interior (closure A) ⊆ closure (interior (closure A)))