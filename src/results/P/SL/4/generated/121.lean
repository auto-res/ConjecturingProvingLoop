

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP1 : Topology.P1 A := Topology.P2_imp_P1 (A := A) hP2
  exact Topology.P1_imp_P1_closure (A := A) hP1