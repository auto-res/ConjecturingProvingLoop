

theorem dense_imp_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P3 (closure A) := by
  intro hDense
  have hP2 : Topology.P2 (closure A) :=
    dense_imp_P2_closure (A := A) hDense
  exact Topology.P2_imp_P3 (A := closure A) hP2