

theorem Topology.P2_closure_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (A : Set X)) →
      Topology.P1 (X := X) (closure (A : Set X)) := by
  intro hP2cl
  exact
    Topology.P2_implies_P1
      (X := X) (A := closure (A : Set X)) hP2cl