

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First, `interior (closure (interior A))` is contained in `closure (interior A)`.
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- Next, `closure (interior A)` is contained in `closure A`.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    closure_mono interior_subset
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂