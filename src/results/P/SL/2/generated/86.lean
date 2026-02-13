

theorem Topology.isOpen_P1_iff_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ↔ Topology.P3 A) := by
  intro hOpen
  have h₁ := (Topology.isOpen_P1_iff_P2 (A := A) hOpen)
  have h₂ := (Topology.isOpen_P2_iff_P3 (A := A) hOpen)
  simpa using h₁.trans h₂