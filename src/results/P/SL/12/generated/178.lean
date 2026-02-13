

theorem Topology.interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) ⊆ closure (interior (closure A)) := by
  -- Step 1: enlarge `interior A` to `interior (closure A)` using monotonicity
  -- of `interior` with respect to the inclusion `A ⊆ closure A`.
  have h₁ :
      (interior (A : Set X)) ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  -- Step 2: every set is contained in the closure of itself.
  have h₂ :
      (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂