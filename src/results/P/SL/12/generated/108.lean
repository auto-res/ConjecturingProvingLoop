

theorem Topology.closure_eq_univ_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔
      interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro h_cl
    -- Rewrite the left-hand side in the desired equality.
    simpa [h_cl, interior_univ]
  · intro h_int
    -- From `interior (closure A) = univ` we get `univ ⊆ closure A`.
    have h_sub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      have : interior (closure (A : Set X)) ⊆ closure A := interior_subset
      simpa [h_int] using this
    -- The reverse inclusion is trivial.
    have h_sup : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro x _; simp
    exact Set.Subset.antisymm h_sup h_sub