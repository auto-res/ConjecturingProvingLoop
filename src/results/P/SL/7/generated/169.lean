

theorem Topology.P1_iff_P3_singleton_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {x : X} :
    Topology.P1 ({x} : Set X) ↔ Topology.P3 ({x} : Set X) := by
  have h₁ := (Topology.P1_singleton_iff_isOpen_of_T1 (x := x))
  have h₃ := (Topology.P3_singleton_iff_isOpen_of_T1 (x := x))
  simpa using h₁.trans h₃.symm