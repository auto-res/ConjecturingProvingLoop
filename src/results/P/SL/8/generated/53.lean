

theorem denseInterior_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P3 A := by
  dsimp [Topology.P3]
  -- First, show that `closure A = univ`.
  have h_closure_eq_univ : closure A = (Set.univ : Set X) := by
    -- `closure (interior A)` is contained in `closure A`, but it is `univ`.
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      simpa [h_dense] using
        (closure_mono (interior_subset : interior A ⊆ A))
    -- The reverse inclusion is trivial.
    exact Set.Subset.antisymm (Set.subset_univ _) h_subset
  -- Hence the interior of `closure A` is also all of `univ`.
  have h_int_eq_univ : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closure_eq_univ, interior_univ]
  -- Finally, establish the required inclusion.
  intro x hx
  have : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_int_eq_univ] using this