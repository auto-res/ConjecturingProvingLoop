

theorem Topology.closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  -- First, we reuse an existing inclusion for interiors.
  have hSub :
      (interior (closure (interior A)) : Set X) ⊆
        closure (interior (closure A)) :=
    Topology.interior_closure_interior_subset_closure_interior_closure (A := A)
  -- Monotonicity of `closure` upgrades the inclusion.
  have hClos :
      closure (interior (closure (interior A))) ⊆
        closure (closure (interior (closure A))) :=
    closure_mono hSub
  -- Simplify the right‐hand closure of a closure.
  simpa [closure_closure] using hClos