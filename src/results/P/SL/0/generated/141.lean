

theorem interior_closure_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ] using
    (interior_univ : interior (Set.univ : Set X) = (Set.univ : Set X))