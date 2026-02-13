

theorem Topology.closure_interior_eq_of_isOpen_isClosed {X : Type*}
    [TopologicalSpace X] {A : Set X} (hOpen : IsOpen A) (hClosed : IsClosed A) :
    closure (interior A) = A := by
  calc
    closure (interior A) = closure A := by
      simpa [hOpen.interior_eq]
    _ = A := hClosed.closure_eq