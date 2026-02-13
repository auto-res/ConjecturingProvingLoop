

theorem Topology.P2_implies_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A ∧ Topology.P3 (X := X) A := by
  intro hP2
  exact
    ⟨Topology.P2_implies_P1 (X := X) (A := A) hP2,
      Topology.P2_implies_P3 (X := X) (A := A) hP2⟩