

theorem P1_subset_closureInterior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP1 : Topology.P1 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  dsimp [Topology.P1] at hP1
  have h_closureInt : closure (interior A) ⊆ closure (interior B) := by
    have h_int : interior A ⊆ interior B := interior_mono hAB
    exact closure_mono h_int
  exact Set.Subset.trans hP1 h_closureInt