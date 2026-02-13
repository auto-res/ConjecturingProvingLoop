

theorem closure_eq_self_iff_isClosed_set {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = A ↔ IsClosed A := by
  constructor
  · intro h_eq
    -- `closure A` is always closed, and it coincides with `A`.
    have h_closed : IsClosed (closure (A : Set X)) := isClosed_closure
    simpa [h_eq] using h_closed
  · intro h_closed
    -- A closed set is equal to its closure.
    simpa using h_closed.closure_eq