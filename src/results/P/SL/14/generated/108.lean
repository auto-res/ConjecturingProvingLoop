

theorem Topology.closureInterior_isClosed
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  simpa using (isClosed_closure : IsClosed (closure (interior A)))