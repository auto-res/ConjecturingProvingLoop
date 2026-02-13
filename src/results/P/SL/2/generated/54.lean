

theorem Topology.P2_nonempty_implies_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 A → A.Nonempty → (interior A).Nonempty := by
  intro hP2 hA_nonempty
  have hP1 : Topology.P1 A := Topology.P2_implies_P1 (A := A) hP2
  exact
    Topology.P1_nonempty_implies_interior_nonempty (A := A) hP1 hA_nonempty