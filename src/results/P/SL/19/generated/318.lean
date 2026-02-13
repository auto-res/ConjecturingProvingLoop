

theorem Topology.closure_eq_self_iff_isClosed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = A ↔ IsClosed A := by
  constructor
  · intro hEq
    have hClosed : IsClosed (closure A) := isClosed_closure (s := A)
    simpa [hEq] using hClosed
  · intro hClosed
    simpa using hClosed.closure_eq