

theorem Topology.closure_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure A = (∅ : Set X) ↔ A = (∅ : Set X) := by
  constructor
  · intro h
    have h₁ : A ⊆ (∅ : Set X) := by
      intro x hx
      have : (x : X) ∈ closure A := subset_closure hx
      simpa [h] using this
    exact Set.Subset.antisymm h₁ (Set.empty_subset _)
  · intro hA
    simpa [hA, closure_empty]