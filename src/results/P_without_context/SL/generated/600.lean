

theorem P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) A → Topology.P1 (X := X) A :=
by
  intro hA
  dsimp [Topology.P2, Topology.P1] at *
  exact hA.trans interior_subset