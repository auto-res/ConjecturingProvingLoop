

theorem Topology.interior_closure_eq_of_isClosed_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    interior (closure A) = A := by
  simpa [hA_closed.closure_eq, hA_open.interior_eq]