

theorem Topology.subset_closureInterior_of_subset_P1 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP1 : Topology.P1 B) :
    A ⊆ closure (interior B) := by
  intro x hxA
  exact hP1 (hAB hxA)