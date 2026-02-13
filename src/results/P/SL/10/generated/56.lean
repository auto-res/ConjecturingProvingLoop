

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) := interior_subset
  have h₂ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  exact Set.Subset.trans h₁ h₂