

theorem Topology.interiorClosureInterior_subset_closure {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior (closure (interior A)) ⊆ closure (A : Set X) := by
  -- First, we use the established inclusion
  -- `interior (closure (interior A)) ⊆ interior (closure A)`.
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    interiorClosureInterior_subset_interiorClosure (A := A)
  -- Next, we recall that `interior (closure A)` is contained in `closure A`.
  have h₂ : interior (closure A) ⊆ closure A := interior_subset
  -- Chaining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂