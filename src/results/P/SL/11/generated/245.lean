

theorem closure_interior_eq_self_iff_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = interior A ↔ IsClosed (interior A) := by
  constructor
  · intro hEq
    have hClosed : IsClosed (closure (interior A)) := isClosed_closure
    simpa [hEq] using hClosed
  · intro hClosed
    simpa using hClosed.closure_eq