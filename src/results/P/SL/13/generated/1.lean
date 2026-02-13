

theorem Topology.P2_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X:=X) A → Topology.P1 (X:=X) A := by
  intro hP2
  dsimp [Topology.P1, Topology.P2] at hP2 ⊢
  intro x hx
  exact interior_subset (hP2 hx)