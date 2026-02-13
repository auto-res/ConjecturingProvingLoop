

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure (A : Set X)) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 hP2
  exact Topology.P1_closure (A := A) hP1