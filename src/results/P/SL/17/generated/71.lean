

theorem Topology.closure_interior_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_subset : A ⊆ B) :
    closure (interior A) ⊆ closure (interior B) := by
  exact closure_mono (interior_mono h_subset)