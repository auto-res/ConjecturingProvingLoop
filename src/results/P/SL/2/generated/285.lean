

theorem Topology.isClosed_of_closure_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior A) = (A : Set X) → IsClosed A := by
  intro hEq
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [hEq] using hClosed