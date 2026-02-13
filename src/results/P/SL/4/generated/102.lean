

theorem closure_interior_closure_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (closure (Set.univ : Set X))) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]