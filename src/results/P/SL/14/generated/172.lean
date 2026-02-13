

theorem Topology.P2_closureInterior_iff_P3_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ :=
    Topology.P2_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  have h₂ :=
    Topology.P3_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  simpa using h₁.trans h₂.symm