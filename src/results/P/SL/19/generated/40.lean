

theorem Topology.univ_is_P1_and_P2_and_P3 {X : Type*} [TopologicalSpace X] :
    Topology.P1 (A := (Set.univ : Set X)) ∧
      Topology.P2 (A := (Set.univ : Set X)) ∧
      Topology.P3 (A := (Set.univ : Set X)) := by
  constructor
  · dsimp [Topology.P1]
    intro x _
    simp [interior_univ, closure_univ]
  · constructor
    · dsimp [Topology.P2]
      intro x _
      simp [interior_univ, closure_univ]
    · dsimp [Topology.P3]
      intro x _
      simp [interior_univ, closure_univ]