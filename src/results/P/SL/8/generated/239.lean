

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Since `interior (closure (interior A)) ⊆ closure (interior A)`,
    -- we obtain the reverse inclusion from the hypothesis.
    have h_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [hInt] using
        (interior_subset :
          interior (closure (interior A)) ⊆ closure (interior A))
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  · intro hCl
    -- Rewrite the left‐hand side using `hCl` and compute the interior of `univ`.
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [hCl]
    simpa [interior_univ] using this