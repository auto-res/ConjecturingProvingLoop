

theorem Topology.dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A ↔ interior (closure A) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    simpa [hDense.closure_eq, interior_univ]
  · intro hInt
    have h_subset : (Set.univ : Set X) ⊆ closure A := by
      intro x hx
      have hxInt : x ∈ interior (closure A) := by
        simpa [hInt] using hx
      exact (interior_subset : interior (closure A) ⊆ closure A) hxInt
    have h_closure_eq : closure A = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · intro _ _; simp
      · exact h_subset
    simpa using (dense_iff_closure_eq).2 h_closure_eq