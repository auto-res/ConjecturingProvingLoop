

theorem Topology.dense_interior_implies_P1_P2_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (interior (A : Set X)) →
      (Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A) := by
  intro hDense
  exact
    ⟨Topology.dense_interior_implies_P1 (A := A) hDense,
      Topology.dense_interior_implies_P2 (A := A) hDense,
      Topology.dense_interior_implies_P3 (A := A) hDense⟩