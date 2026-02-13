

theorem P1_closure_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → Topology.P1 (closure (A : Set X)) := by
  intro hA
  have hP1 : Topology.P1 (A : Set X) :=
    Topology.P2_implies_P1 (A := A) hA
  exact Topology.P1_closure (A := A) hP1