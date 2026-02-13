

theorem Topology.closure_interior_eq_univ_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (Set.univ : Set X) ↔
      interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro h
    have : interior (closure (interior A)) =
        interior (Set.univ : Set X) := by
      simpa [h]
    simpa [interior_univ] using this
  · intro h
    -- `interior S ⊆ S` for any set `S`
    have h_subset : interior (closure (interior A)) ⊆
        closure (interior A) := interior_subset
    -- Using `h`, this gives `univ ⊆ closure (interior A)`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [h]
        using (show interior (closure (interior A)) ⊆ closure (interior A) from h_subset)
    -- The reverse inclusion is trivial.
    have h_subset_univ : closure (interior A) ⊆ (Set.univ : Set X) := by
      intro _ _; simp
    exact Set.Subset.antisymm h_subset_univ h_univ_subset