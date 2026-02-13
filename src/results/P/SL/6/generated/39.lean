

theorem P2_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hP2
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hP2
  exact Topology.P1_closure_of_P1 (A := A) hP1