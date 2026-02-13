

theorem Topology.isOpen_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen A → (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hOpen
  exact
    ⟨Topology.isOpen_implies_P1 (A := A) hOpen,
      Topology.isOpen_implies_P2 (A := A) hOpen,
      Topology.isOpen_implies_P3 (A := A) hOpen⟩