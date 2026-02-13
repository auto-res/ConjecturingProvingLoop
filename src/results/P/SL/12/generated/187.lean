

theorem Topology.interior_diff_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior (closure A) := by
  -- First include `A \ B ⊆ A`, then apply monotonicity of `interior`.
  have h₁ : interior (A \ B : Set X) ⊆ interior A :=
    interior_mono (Set.diff_subset : (A \ B : Set X) ⊆ A)
  -- Next, use the general inclusion `interior A ⊆ interior (closure A)`.
  have h₂ : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (X := X) (A := A)
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂