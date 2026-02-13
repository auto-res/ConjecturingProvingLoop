

theorem P1_subset_of_closureInterior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hsubset : closure (interior A) ⊆ B) :
    A ⊆ B := by
  dsimp [Topology.P1] at hP1
  intro x hxA
  exact hsubset (hP1 hxA)