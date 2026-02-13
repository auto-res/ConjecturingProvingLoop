

theorem Topology.P3_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P3 A := by
  intro hP3
  exact Topology.P3_of_P3_closure (A := A) hP3