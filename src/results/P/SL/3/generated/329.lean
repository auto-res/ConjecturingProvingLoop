

theorem interior_closure_eq_univ_of_dense_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (A : Set X)) = (Set.univ : Set X) →
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  intro hDenseInt
  -- First, rewrite `interior (closure (interior A))` using the density assumption.
  have hIntUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) := by
    have :
        interior (closure (interior (A : Set X))) =
          interior ((Set.univ : Set X)) := by
      simpa [hDenseInt]
    simpa [interior_univ] using this
  -- Monotonicity of `interior` with respect to set inclusion.
  have hSubset :
      interior (closure (interior (A : Set X))) ⊆
        interior (closure (A : Set X)) := by
    apply interior_mono
    exact closure_interior_subset_closure (A := A)
  -- Since the left‐hand side is `univ`, the right‐hand side is also `univ`.
  have hUniv :
      (Set.univ : Set X) ⊆ interior (closure (A : Set X)) := by
    simpa [hIntUniv] using hSubset
  -- Conclude the desired equality.
  exact Set.Subset.antisymm (Set.subset_univ _) hUniv