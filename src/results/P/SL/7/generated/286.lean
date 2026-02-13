

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (interior A) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- We prove both inclusions separately.
  apply Set.Subset.antisymm
  · -- `closure A ⊆ univ` is trivial.
    exact Set.Subset_univ _
  · -- To show `univ ⊆ closure A`, start with an arbitrary point `x`.
    intro x _
    -- Using the hypothesis `h`, we have `x ∈ closure (interior A)`.
    have hx_closureInt : x ∈ closure (interior A) := by
      have : x ∈ (Set.univ : Set X) := by
        simp
      simpa [h] using this
    -- Since `interior A ⊆ A`, taking closures gives the required inclusion.
    have hIncl : closure (interior A) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : interior A ⊆ A)
    exact hIncl hx_closureInt