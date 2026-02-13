

theorem Topology.closureInterior_eq_of_isClopen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_open : IsOpen A) (hA_closed : IsClosed A) :
    closure (interior A) = (A : Set X) := by
  calc
    closure (interior A) = closure A := by
      simpa [hA_open.interior_eq]
    _ = A := by
      simpa [hA_closed.closure_eq]