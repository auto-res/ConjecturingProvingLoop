

theorem Topology.closure_interior_eq_univ_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) ↔
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
  simpa using
    (Topology.closure_eq_univ_iff_interior_closure_eq_univ
      (X := X) (A := interior A))