

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  simpa using
    (Topology.interior_closure_eq_univ_iff_closure_eq_univ
      (X := X) (A := interior A))