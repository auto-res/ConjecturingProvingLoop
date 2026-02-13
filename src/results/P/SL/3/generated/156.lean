

theorem closure_closure_diff_interior_eq_self {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    closure (closure (A : Set X) \ interior (A : Set X)) =
      closure (A : Set X) \ interior (A : Set X) := by
  have hClosed :
      IsClosed (closure (A : Set X) \ interior (A : Set X)) :=
    isClosed_closure_diff_interior (A := A)
  simpa using hClosed.closure_eq