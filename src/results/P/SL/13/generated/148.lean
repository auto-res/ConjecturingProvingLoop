

theorem Topology.closure_interior_closure_interior_closure_subset_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) ⊆
      closure A := by
  -- First, reduce to `closure (interior (closure A))`.
  have h₁ :
      closure (interior (closure (interior (closure (A : Set X))))) ⊆
        closure (interior (closure (A : Set X))) :=
    Topology.closure_interior_closure_subset_closure
      (X := X) (A := interior (closure (A : Set X)))
  -- Then, relate this to `closure A`.
  have h₂ :
      closure (interior (closure (A : Set X))) ⊆ closure A :=
    Topology.closure_interior_closure_subset_closure (X := X) (A := A)
  exact Set.Subset.trans h₁ h₂