

theorem Topology.P1_closure_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P1 (closure A) := by
  intro hDense
  have hP3 : Topology.P3 A := Topology.P3_of_dense_interior (A := A) hDense
  exact Topology.P1_closure_of_P3 (A := A) hP3