

theorem Topology.closureInterior_isClosed {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsClosed (closure (interior A)) := by
  -- The closure of any set is closed.
  simpa using (isClosed_closure : IsClosed (closure (interior A)))