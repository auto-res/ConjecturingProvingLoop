

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, `interior S ⊆ closure S` for any set `S`.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Second, we already have `closure (interior A) ⊆ closure (interior (closure A))`.
  have h₂ : closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  -- Compose the two inclusions.
  exact Set.Subset.trans h₁ h₂