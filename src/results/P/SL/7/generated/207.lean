

theorem Topology.closureInteriorClosureInterior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure (A : Set X) := by
  -- `interior (closure (interior A)) ⊆ closure (interior A)`
  have h₁ : interior (closure (interior A)) ⊆ closure (interior A) :=
    interior_subset
  -- `closure (interior A) ⊆ closure A`
  have h₂ : (closure (interior A) : Set X) ⊆ closure (A : Set X) :=
    closure_mono (interior_subset : interior A ⊆ A)
  -- Combine the two inclusions.
  have h₃ : interior (closure (interior A)) ⊆ closure (A : Set X) :=
    Set.Subset.trans h₁ h₂
  -- Taking closures preserves inclusion.
  have h₄ :
      closure (interior (closure (interior A))) ⊆
        closure (closure (A : Set X)) :=
    closure_mono h₃
  -- Simplify using idempotence of `closure`.
  simpa [closure_closure] using h₄