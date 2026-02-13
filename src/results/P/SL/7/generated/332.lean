

theorem Topology.isClosed_of_closureInterior_eq
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (A : Set X)) :
    IsClosed (A : Set X) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa [h] using hClosed