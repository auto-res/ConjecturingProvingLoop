

theorem Topology.dense_interior_iff_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) ↔ interior (closure (interior A)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      simpa using hDense.closure_eq
    simpa [hcl, interior_univ]
  · intro hIntEq
    -- First, show that `closure (interior A)` is the whole space.
    have hsubset : (Set.univ : Set X) ⊆ closure (interior A) := by
      intro x _
      have hx : x ∈ interior (closure (interior A)) := by
        simpa [hIntEq]
      exact (interior_subset : interior (closure (interior A)) ⊆ closure (interior A)) hx
    have hcl : closure (interior A) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact hsubset
    -- Conclude density from the equality of closures.
    exact (dense_iff_closure_eq).2 hcl