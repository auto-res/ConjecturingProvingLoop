

theorem Topology.P1_iff_P3_finite_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ Topology.P3 F := by
  have h₁ : Topology.P1 F ↔ IsOpen F :=
    Topology.P1_finite_iff_isOpen_of_T1 (F := F) hF
  have h₂ : Topology.P3 F ↔ IsOpen F :=
    Topology.P3_finite_iff_isOpen_of_T1 (F := F) hF
  simpa using h₁.trans h₂.symm