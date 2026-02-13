

theorem Topology.P2_iff_P3_of_closureInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (interior A)) ↔ Topology.P3 (closure (interior A)) := by
  have h₁ := (Topology.P2_closureInterior_iff_isOpen (A := A))
  have h₂ := (Topology.P3_closureInterior_iff_isOpen (A := A))
  simpa using h₁.trans h₂.symm