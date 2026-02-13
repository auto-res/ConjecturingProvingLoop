

theorem exists_open_superset_same_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A →
      ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U = closure A := by
  intro hP2
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact exists_open_superset_same_closure_of_P3 (A := A) hP3