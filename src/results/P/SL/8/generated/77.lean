

theorem closure_eq_univ_of_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  ·
    have h : closure (interior A) ⊆ closure A :=
      closure_mono (interior_subset : interior A ⊆ A)
    simpa [h_dense] using h