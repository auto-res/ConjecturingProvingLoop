

theorem Topology.closure_interior_eq_self_of_clopen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hClosed : IsClosed A) (hOpen : IsOpen A) :
    closure (interior A) = A := by
  simpa [hOpen.interior_eq, hClosed.closure_eq]