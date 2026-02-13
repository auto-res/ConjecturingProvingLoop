

theorem Topology.P2_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P2 F ↔ IsOpen F := by
  have hClosed : IsClosed (F : Set X) := hF.isClosed
  simpa using (Topology.P2_closed_iff_isOpen (A := F) hClosed)