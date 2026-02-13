

theorem Topology.P2_of_P3_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure (A : Set X)) → Topology.P2 (closure A) := by
  intro hP3
  exact ((Topology.P2_closure_iff_P3_closure (X := X) (A := A)).2) hP3