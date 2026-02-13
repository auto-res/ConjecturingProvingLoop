

theorem Topology.interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure (interior (closure A)) := by
  -- First, we use an existing lemma to go from
  -- `interior (closure (interior A))` to `interior (closure A)`.
  have h₁ : interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure (A := A)
  -- Next, every set is contained in the closure of itself.
  have h₂ : interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combining the two inclusions gives the desired result.
  exact Set.Subset.trans h₁ h₂