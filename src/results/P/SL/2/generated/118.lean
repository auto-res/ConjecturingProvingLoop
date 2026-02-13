

theorem Topology.P2_nonempty_implies_interior_closure_nonempty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior (closure A)).Nonempty := by
  intro hP2 hA_nonempty
  have hP3 : Topology.P3 A := Topology.P2_implies_P3 (A := A) hP2
  exact
    Topology.P3_nonempty_implies_interior_closure_nonempty
      (A := A) hP3 hA_nonempty