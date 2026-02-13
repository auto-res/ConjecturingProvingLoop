

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  apply subset_antisymm
  ·
    exact Set.subset_univ _
  ·
    have : (Set.univ : Set X) ⊆ closure A := by
      simpa [hDense] using
        (closure_mono (interior_subset : interior A ⊆ A))
    exact this