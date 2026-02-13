

theorem dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) ↔
      interior (closure (interior (A : Set X))) = Set.univ := by
  simpa using
    (Topology.dense_iff_interior_closure_eq_univ
      (A := interior (A : Set X)))