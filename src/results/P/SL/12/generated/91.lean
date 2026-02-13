

theorem Topology.interior_closure_eq_self_of_isClosed_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_closed : IsClosed (A : Set X)) (h_open : IsOpen (A : Set X)) :
    interior (closure (A : Set X)) = A := by
  simpa [h_closed.closure_eq, h_open.interior_eq]