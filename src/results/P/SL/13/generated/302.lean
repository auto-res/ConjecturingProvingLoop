

theorem Topology.isClosed_interior_iff_closureInterior_eq_interior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = interior A := by
  constructor
  · intro hClosed
    simpa using hClosed.closure_eq
  · intro hEq
    have hClosed : IsClosed (closure (interior (A : Set X))) :=
      isClosed_closure
    simpa [hEq] using hClosed