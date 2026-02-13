

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    closure A = (Set.univ : Set X) := by
  -- First, density gives `closure (interior A) = Set.univ`.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Since `interior A ⊆ A`, their closures satisfy
  -- `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence `Set.univ ⊆ closure A`.
  have h_superset : (Set.univ : Set X) ⊆ closure A := by
    simpa [h_closure_int] using h_subset
  -- The opposite inclusion is trivial.
  have h_subset_univ : closure A ⊆ (Set.univ : Set X) := by
    intro _x _hx; simp
  -- Conclude by antisymmetry.
  exact Set.Subset.antisymm h_subset_univ h_superset