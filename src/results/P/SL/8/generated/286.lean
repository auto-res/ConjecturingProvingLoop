

theorem interior_closureInterior_subset_closureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior A) := by
  simpa using
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A))