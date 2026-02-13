

theorem Topology.closure_eq_univ_of_dense_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- `closure (interior A)` is always contained in `closure A`.
  have h_subset : (closure (interior (A : Set X))) ⊆ closure A :=
    closure_mono (interior_subset : (interior (A : Set X)) ⊆ A)
  -- Hence, from the hypothesis, `univ ⊆ closure A`.
  have h_univ_subset : (Set.univ : Set X) ⊆ closure A := by
    simpa [hA] using h_subset
  -- The reverse inclusion is immediate.
  have h_closure_subset : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro x _; simp
  -- Conclude the desired equality.
  exact Set.Subset.antisymm h_closure_subset h_univ_subset