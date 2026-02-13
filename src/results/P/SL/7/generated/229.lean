

theorem Topology.closureInteriorClosureInterior_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- First, relate the interiors of the two sets.
  have h₁ :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    interiorClosureInterior_subset_interiorClosure (A := A)
  -- Next, every set is contained in the closure of itself.
  have h₂ :
      interior (closure A) ⊆ closure (interior (closure A)) :=
    subset_closure
  -- Combine the two inclusions.
  have hIncl :
      interior (closure (interior A)) ⊆ closure (interior (closure A)) :=
    Set.Subset.trans h₁ h₂
  -- Taking closures preserves inclusions; simplify the right‐hand side.
  simpa [closure_closure] using closure_mono hIncl