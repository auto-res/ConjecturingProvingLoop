

theorem Topology.interior_closure_interior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    interior (closure (interior A)) = A := by
  have h_open : IsOpen A := isOpen_discrete _
  have h_closed : IsClosed A := isClosed_discrete _
  simp [h_open.interior_eq, h_closed.closure_eq]