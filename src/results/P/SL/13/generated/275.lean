

theorem Topology.closure_eq_univ_iff_forall_mem {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) = (Set.univ : Set X) ↔ ∀ x : X, x ∈ closure (A : Set X) := by
  constructor
  · intro h x
    have : (x : X) ∈ (Set.univ : Set X) := by
      simp
    simpa [h] using this
  · intro h
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      exact h x