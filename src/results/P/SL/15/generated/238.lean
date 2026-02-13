

theorem dense_closed_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) (hClosed : IsClosed A) :
    A = (Set.univ : Set X) := by
  -- The density of `A` gives `closure A = univ`.
  have hClosure : closure A = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Since `A` is closed, `closure A = A`.
  have hClosedEq : closure A = A := hClosed.closure_eq
  -- Combine the two equalities to obtain the result.
  simpa [hClosedEq] using hClosure