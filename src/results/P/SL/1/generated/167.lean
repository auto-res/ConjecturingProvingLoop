

theorem Topology.interior_closure_interior_univ_eq_univ
    {X : Type*} [TopologicalSpace X] :
    interior (closure (interior (Set.univ : Set X))) = (Set.univ : Set X) := by
  simp [interior_univ, closure_univ]