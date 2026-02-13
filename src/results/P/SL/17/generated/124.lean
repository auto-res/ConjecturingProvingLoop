

theorem Topology.dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  simpa using
    (Topology.dense_iff_interior_closure_eq_univ (A := interior A))