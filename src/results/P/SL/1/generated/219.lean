

theorem Topology.isClosed_of_closure_interior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) :
    IsClosed A := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using hClosed