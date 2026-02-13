

theorem Topology.P1_P2_P3_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    (Topology.P1 F ∧ Topology.P2 F ∧ Topology.P3 F) ↔ IsOpen F := by
  have hP1 := Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have hP2 := Topology.P2_finite_iff_isOpen_of_T1 (F := F) hF
  have hP3 := Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  constructor
  · intro hTriple
    exact (hP1).1 hTriple.1
  · intro hOpen
    exact ⟨(hP1).2 hOpen, (hP2).2 hOpen, (hP3).2 hOpen⟩