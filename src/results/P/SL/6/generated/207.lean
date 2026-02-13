

theorem P2_closure_implies_P1_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 (closure (A : Set X)) :=
    Topology.P2_implies_P1 (A := closure (A : Set X)) hP2
  simpa using hP1