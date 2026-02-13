

theorem Topology.closure_interior_closure_subset_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (A : Set X))) ⊆ closure A := by
  -- First, note that `interior (closure A)` is contained in `closure A`.
  have h_subset : interior (closure (A : Set X)) ⊆ closure A :=
    interior_subset
  -- Taking closures on both sides preserves the inclusion.
  have h_closure :
      closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
    closure_mono h_subset
  -- Simplify the right‐hand side using `closure_closure`.
  simpa [closure_closure] using h_closure