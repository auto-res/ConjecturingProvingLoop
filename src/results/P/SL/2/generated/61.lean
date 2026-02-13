

theorem Topology.dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P1 (closure (A : Set X)) := by
  intro hDense
  have hP3 : Topology.P3 (A : Set X) := Topology.dense_implies_P3 (A := A) hDense
  exact Topology.P1_closure_of_P3 (A := A) hP3