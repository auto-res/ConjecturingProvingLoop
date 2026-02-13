

theorem closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) →
      closure (A : Set X) = (Set.univ : Set X) := by
  intro h_dense_int
  -- `closure (interior A)` is always contained in `closure A`
  have h_subset : closure (interior (A : Set X)) ⊆ closure A :=
    closure_mono (interior_subset (s := A))
  -- Hence `Set.univ ⊆ closure A`
  have : (Set.univ : Set X) ⊆ closure A := by
    simpa [h_dense_int] using h_subset
  -- Combine the two inclusions to obtain equality
  exact Set.Subset.antisymm (Set.subset_univ _) this