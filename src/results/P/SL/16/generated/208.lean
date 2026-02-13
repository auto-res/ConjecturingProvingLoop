

theorem Topology.isClosed_iff_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A ↔ closure A = A := by
  constructor
  · intro hClosed
    simpa using hClosed.closure_eq
  · intro hEq
    have hClosedCl : IsClosed (closure A) := isClosed_closure
    simpa [hEq] using hClosedCl