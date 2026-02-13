

theorem dense_imp_P1_P2_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → (Topology.P1 (closure A) ∧ Topology.P2 (closure A) ∧ Topology.P3 (closure A)) := by
  intro hDense
  have hP1 : Topology.P1 (closure A) := dense_imp_P1_closure (A := A) hDense
  have hP2 : Topology.P2 (closure A) := dense_imp_P2_closure (A := A) hDense
  have hP3 : Topology.P3 (closure A) := dense_imp_P3_closure (A := A) hDense
  exact And.intro hP1 (And.intro hP2 hP3)