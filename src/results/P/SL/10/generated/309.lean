

theorem Topology.P2_subset_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ interior (closure A) := by
  intro hP2
  have hP3 : Topology.P3 A :=
    Topology.P2_implies_P3 (X := X) (A := A) hP2
  dsimp [Topology.P3] at hP3
  exact hP3