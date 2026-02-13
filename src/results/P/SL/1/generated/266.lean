

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  -- First, `interior A ⊆ interior (closure A)` by monotonicity of `interior`.
  have h₁ : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Second, every set is contained in the closure of itself.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) := by
    intro x hx
    exact subset_closure hx
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂