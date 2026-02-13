

theorem Topology.P3_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P3 F ↔ IsOpen F := by
  have hClosed : IsClosed (F : Set X) := by
    exact hF.isClosed
  simpa using (Topology.P3_closed_iff_isOpen (A := F) hClosed)