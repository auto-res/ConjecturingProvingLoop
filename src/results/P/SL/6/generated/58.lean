

theorem P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → (Topology.P1 A ∧ Topology.P3 A) := by
  intro hP2
  exact
    ⟨Topology.P2_implies_P1 (A := A) hP2,
      Topology.P2_implies_P3 (A := A) hP2⟩