

theorem Topology.P1_P2_P3_univ {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    intro x hx
    simpa [interior_univ, closure_univ] using hx
  · dsimp [Topology.P2]
    intro x hx
    simpa [interior_univ, closure_univ] using hx
  · dsimp [Topology.P3]
    intro x hx
    simpa [interior_univ, closure_univ] using hx