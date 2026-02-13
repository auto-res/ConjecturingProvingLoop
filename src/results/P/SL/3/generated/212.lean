

theorem isClosed_interior_iff_closure_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsClosed (interior (A : Set X)) ↔
      closure (interior (A : Set X)) = interior (A : Set X) := by
  constructor
  · intro hClosed
    simpa [hClosed.closure_eq]
  · intro hEq
    have hClosed_closure : IsClosed (closure (interior (A : Set X))) := isClosed_closure
    simpa [hEq] using hClosed_closure