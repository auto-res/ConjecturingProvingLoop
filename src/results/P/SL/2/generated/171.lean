

theorem Topology.dense_implies_P1_P2_P3_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense A →
      (Topology.P1 (closure (A : Set X)) ∧
        Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) := by
  intro hDense
  exact
    ⟨Topology.dense_implies_P1_closure (A := A) hDense,
      Topology.dense_implies_P2_closure (A := A) hDense,
      Topology.dense_implies_P3_closure (A := A) hDense⟩