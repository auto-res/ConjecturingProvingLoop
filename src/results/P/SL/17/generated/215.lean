

theorem Topology.closed_dense_iff_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed A) :
    Dense A ↔ interior A = (Set.univ : Set X) := by
  constructor
  · intro hDense
    -- Since `A` is both closed and dense, it is the whole space.
    have h_eq : A = (Set.univ : Set X) :=
      Topology.closed_dense_eq_univ (A := A) hA_closed hDense
    -- Rewriting `interior A` along this equality yields the result.
    simpa [h_eq, interior_univ] using
      (interior_univ : interior (Set.univ : Set X) = Set.univ)
  · intro hInt
    -- From `interior A = univ` we get `A = univ`.
    have h_subset : (Set.univ : Set X) ⊆ A := by
      have : interior A ⊆ A := interior_subset
      simpa [hInt] using this
    have h_eq : A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_subset
    -- The whole space is dense, hence so is `A`.
    simpa [h_eq] using (dense_univ : Dense (Set.univ : Set X))