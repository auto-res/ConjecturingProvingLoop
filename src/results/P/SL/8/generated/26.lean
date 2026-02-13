

theorem denseInterior_imp_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 A := by
  dsimp [Topology.P1]
  have : A ⊆ (Set.univ : Set X) := Set.subset_univ _
  simpa [h_dense] using this