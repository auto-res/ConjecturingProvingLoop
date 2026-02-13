

theorem Topology.isClosed_P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClosed A → (Topology.P2 A ↔ (Topology.P1 A ∧ Topology.P3 A)) := by
  intro hClosed
  have h₁ := (Topology.isClosed_P2_iff_isOpen (A := A) hClosed)
  have h₂ := (Topology.isClosed_isOpen_iff_P1_and_P3 (A := A) hClosed)
  simpa using h₁.trans h₂