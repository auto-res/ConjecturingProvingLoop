

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure A)) ⊆ closure A := by
  have h₁ : interior (closure A) ⊆ closure A := interior_subset
  have h₂ : closure (interior (closure A)) ⊆ closure (closure A) :=
    closure_mono h₁
  simpa [closure_closure] using h₂