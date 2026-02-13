

theorem Topology.interiorClosureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  exact interior_subset