

theorem Topology.P2_iff_P3_singleton_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P2 ({x} : Set X) ↔ Topology.P3 ({x} : Set X) := by
  have hP2 : Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P2_singleton_iff_isOpen_of_T1 (x := x)
  have hP3 : Topology.P3 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P3_singleton_iff_isOpen_of_T1 (x := x)
  simpa using hP2.trans hP3.symm