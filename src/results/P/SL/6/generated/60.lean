

theorem univ_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] :
    Topology.P1 (Set.univ : Set X) ∧ Topology.P2 (Set.univ : Set X) ∧ Topology.P3 (Set.univ : Set X) := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [Topology.P1]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)
  · dsimp [Topology.P2]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)
  · dsimp [Topology.P3]
    simpa [interior_univ, closure_univ]
      using (subset_rfl : (Set.univ : Set X) ⊆ Set.univ)