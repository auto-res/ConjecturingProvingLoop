

theorem Topology.interior_closure_eq_univ_of_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure A = (Set.univ : Set X)) :
    interior (closure A) = (Set.univ : Set X) := by
  simpa [h, interior_univ]