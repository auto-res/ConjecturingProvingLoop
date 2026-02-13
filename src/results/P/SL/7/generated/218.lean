

theorem Topology.P2_iff_P3_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P2 F ↔ Topology.P3 F := by
  have hP2 : Topology.P2 F ↔ IsOpen F :=
    Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  have hP3 : Topology.P3 F ↔ IsOpen F :=
    Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using hP2.trans hP3.symm