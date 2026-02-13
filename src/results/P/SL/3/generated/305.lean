

theorem isClosed_iff_closure_eq_self {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed (A : Set X) ↔ closure (A : Set X) = A := by
  constructor
  · intro hA_closed
    simpa using hA_closed.closure_eq
  · intro hEq
    have : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [hEq] using this