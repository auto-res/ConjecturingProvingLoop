

theorem Topology.closureInterior_eq_self_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] (A : Set X) :
    closure (interior A) = A := by
  have h_open : IsOpen A := isOpen_discrete _
  have h_closed : IsClosed A := isClosed_discrete _
  have h_int : interior A = A := h_open.interior_eq
  have h_closure : closure A = A := h_closed.closure_eq
  simpa [h_int, h_closure]