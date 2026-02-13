

theorem P2_closureInterior_iff_P3_closureInterior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h_closed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using
    Topology.closed_P2_iff_P3 (X := X) (A := closure (interior A)) h_closed