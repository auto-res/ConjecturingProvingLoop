

theorem closure_eq_self_iff_closed {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = A ↔ IsClosed (A : Set X) := by
  constructor
  · intro h
    exact isClosed_of_closure_eq (A := A) h
  · intro hClosed
    simpa using hClosed.closure_eq