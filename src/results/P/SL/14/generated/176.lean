

theorem Topology.eq_univ_of_isClosed_and_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hDense : Dense (interior A)) :
    (A : Set X) = (Set.univ : Set X) := by
  -- From density we know that the closure of `interior A` is the whole space.
  have h_closure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
  -- Since `A` is closed and contains `interior A`, it contains the closure of `interior A`.
  have h_subset : closure (interior A) ⊆ A :=
    closure_minimal (interior_subset : interior A ⊆ A) hA_closed
  -- Therefore `univ ⊆ A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ A := by
    simpa [h_closure] using h_subset
  -- The reverse inclusion is trivial.
  have h_subset_univ : (A : Set X) ⊆ Set.univ := by
    intro _ _; simp
  exact Set.Subset.antisymm h_subset_univ h_univ_subset