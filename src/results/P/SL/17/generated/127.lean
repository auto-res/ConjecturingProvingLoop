

theorem Topology.closure_interior_univ {X : Type*} [TopologicalSpace X] :
    closure (interior (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [interior_univ] using
    (closure_univ : closure (Set.univ : Set X) = Set.univ)