

theorem Topology.P1_P2_P3_singleton_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    (Topology.P1 ({x} : Set X) ∧ Topology.P2 ({x} : Set X) ∧ Topology.P3 ({x} : Set X))
      ↔ IsOpen ({x} : Set X) := by
  have hP1 : Topology.P1 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P1_singleton_iff_isOpen_of_T1 (x := x)
  have hP2 : Topology.P2 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P2_singleton_iff_isOpen_of_T1 (x := x)
  have hP3 : Topology.P3 ({x} : Set X) ↔ IsOpen ({x} : Set X) :=
    Topology.P3_singleton_iff_isOpen_of_T1 (x := x)
  constructor
  · intro hTriple
    exact (hP1).1 hTriple.1
  · intro hOpen
    exact ⟨(hP1).2 hOpen, (hP2).2 hOpen, (hP3).2 hOpen⟩