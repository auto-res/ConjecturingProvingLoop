

theorem Topology.closure_interior_eq_self_of_clopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hA_open : IsOpen A) :
    closure (interior A) = A := by
  calc
    closure (interior A) = closure A := by
      simpa [hA_open.interior_eq]
    _ = A := hA_closed.closure_eq