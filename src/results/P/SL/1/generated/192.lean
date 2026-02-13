

theorem Topology.closure_interior_subset_closure_of_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior A) ⊆ closure B := by
  -- Since `interior A ⊆ A` and `A ⊆ B`, we get `interior A ⊆ B`.
  have hsubset : (interior A : Set X) ⊆ B :=
    Set.Subset.trans (interior_subset : (interior A : Set X) ⊆ A) hAB
  -- Taking closures preserves set inclusion.
  exact closure_mono hsubset