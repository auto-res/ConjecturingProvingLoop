

theorem Topology.interior_closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hDense : Dense (interior A)) :
    interior (closure A) = (Set.univ : Set X) := by
  -- The density of `interior A` implies its closure is the whole space.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- `closure (interior A)` is contained in `closure A`.
  have h_subset : closure (interior A) ⊆ closure A :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Hence, `closure A` is also the whole space.
  have h_closureA : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _x _hx; simp
    ·
      have : (Set.univ : Set X) ⊆ closure A := by
        have : closure (interior A) ⊆ closure A := h_subset
        simpa [h_closure_int] using this
      exact this
  -- Taking interiors yields the desired equality.
  simpa [h_closureA] using
    (interior_univ : interior (Set.univ : Set X) = Set.univ)