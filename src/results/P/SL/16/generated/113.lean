

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    closure A = (Set.univ : Set X) := by
  -- From `interior A ⊆ A` we get `closure (interior A) ⊆ closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Rewrite the density hypothesis to obtain `univ ⊆ closure A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    intro x _
    have hx : x ∈ closure (interior A) := by
      simpa [h_dense] using (by simp : (x : X) ∈ (Set.univ : Set X))
    exact h_subset hx
  -- Combine the two inclusions.
  apply subset_antisymm
  · intro _ _; simp
  · exact h_univ_subset