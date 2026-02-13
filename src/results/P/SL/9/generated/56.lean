

theorem Topology.interior_closure_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    interior (closure A) = A := by
  have h_closed : IsClosed A := isClosed_discrete _
  have h_open : IsOpen A := isOpen_discrete _
  have h_closure : closure A = A := h_closed.closure_eq
  simpa [h_closure, h_open.interior_eq]