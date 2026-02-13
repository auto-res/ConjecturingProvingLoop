

theorem Topology.disjoint_interior_boundary
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (interior (A : Set X)) (closure A \ interior A) := by
  -- We use the characterization `Set.disjoint_left`.
  exact (Set.disjoint_left).2 (by
    intro x hx_int hx_boundary
    -- `hx_boundary.2` states that `x ∉ interior A`, contradicting `hx_int`.
    exact (hx_boundary.2) hx_int)