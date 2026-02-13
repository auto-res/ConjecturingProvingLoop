

theorem Topology.interiorClosure_eq_interior_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    interior (closure (A : Set X)) = interior A := by
  simpa [hA.closure_eq]