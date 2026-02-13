

theorem Topology.interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    interior A ⊆ interior (closure (interior A)) := by
  -- First, note that `interior A ⊆ closure (interior A)`.
  have h : interior A ⊆ closure (interior A) := subset_closure
  -- Applying the monotonicity of `interior` yields the desired inclusion.
  have h' : interior (interior A) ⊆ interior (closure (interior A)) :=
    interior_mono h
  -- Finally, rewrite `interior (interior A)` to `interior A`.
  simpa [interior_interior] using h'