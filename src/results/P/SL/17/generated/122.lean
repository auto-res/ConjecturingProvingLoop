

theorem Topology.closure_interior_eq_empty_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (∅ : Set X) ↔ interior A = (∅ : Set X) := by
  constructor
  · intro h
    -- First, show `interior A ⊆ ∅`.
    have h_sub : interior A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure (interior A) := subset_closure hx
      simpa [h] using this
    -- From the subset relation, obtain the desired equality.
    have h_eq : interior A = (∅ : Set X) := by
      apply Set.Subset.antisymm
      · exact h_sub
      · exact Set.empty_subset _
    exact h_eq
  · intro h
    simpa [h, closure_empty]