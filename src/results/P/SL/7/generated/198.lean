

theorem Topology.P1_iff_P2_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ Topology.P2 F := by
  have hP1 := Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have hP2 := Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using hP1.trans hP2.symm