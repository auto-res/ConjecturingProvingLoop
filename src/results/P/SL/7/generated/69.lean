

theorem Topology.P2_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) := by
  have hClosed : IsClosed ({x} : Set X) := isClosed_singleton
  simpa using (Topology.P2_closed_iff_isOpen (A := ({x} : Set X)) hClosed)