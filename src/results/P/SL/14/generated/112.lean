

theorem Topology.Subset_closureInterior_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) (hB : Topology.P1 B) :
    (A : Set X) ⊆ closure (interior B) := by
  dsimp [Topology.P1] at hB
  exact Set.Subset.trans hAB hB