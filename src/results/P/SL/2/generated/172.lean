

theorem Topology.closure_interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior (closure (interior A))) ⊆ closure A := by
  -- Step 1: we already know that
  --   `interior (closure (interior A)) ⊆ closure A`.
  have h :
      (interior (closure (interior A)) : Set X) ⊆ closure A :=
    Topology.interior_closure_interior_subset_closure (A := A)
  -- Step 2: taking closures preserves inclusions and `closure (closure A) = closure A`.
  simpa [closure_closure] using closure_mono h