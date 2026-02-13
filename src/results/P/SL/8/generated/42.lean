

theorem P2_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P1 (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  exact Topology.P3_imp_P1_closure (X := X) (A := A) hP3