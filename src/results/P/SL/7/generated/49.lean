

theorem Topology.P2_closureInterior_iff_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ IsOpen (closure (interior A)) := by
  have hClosed : IsClosed (closure (interior A)) := isClosed_closure
  simpa using (Topology.P2_closed_iff_isOpen (A := closure (interior A)) hClosed)