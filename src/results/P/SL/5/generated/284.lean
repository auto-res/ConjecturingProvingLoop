

theorem closure_interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆ closure (A : Set X) := by
  intro x hx
  -- Step 1: `interior (closure (interior A)) ⊆ closure (interior A)`.
  have h₁ : (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
    interior_subset
  -- Hence the same inclusion holds for the closures.
  have hx_clIntA : x ∈ closure (interior A) := by
    have : x ∈ closure (closure (interior A)) :=
      (closure_mono h₁) hx
    simpa [closure_closure] using this
  -- Step 2: `closure (interior A) ⊆ closure A`.
  have h₂ : closure (interior A) ⊆ closure (A : Set X) :=
    Topology.closure_interior_subset_closure (X := X) A
  -- Combine the two steps.
  exact h₂ hx_clIntA