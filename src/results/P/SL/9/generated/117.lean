

theorem Topology.closureInterior_subset_of_isClosed
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) :
    closure (interior A) ⊆ A := by
  have h : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  simpa [hA.closure_eq] using h