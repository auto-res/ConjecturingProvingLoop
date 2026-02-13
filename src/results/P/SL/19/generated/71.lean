

theorem Topology.interior_closure_univ_eq_univ {X : Type*} [TopologicalSpace X] :
    interior (closure (Set.univ : Set X)) = (Set.univ : Set X) := by
  simpa [closure_univ, interior_univ]