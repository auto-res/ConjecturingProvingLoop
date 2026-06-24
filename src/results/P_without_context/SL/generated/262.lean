

theorem Topology.P2_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    P2 (X:=X) A → P1 (X:=X) A := by
  intro h
  dsimp [P2, P1] at *
  exact h.trans interior_subset