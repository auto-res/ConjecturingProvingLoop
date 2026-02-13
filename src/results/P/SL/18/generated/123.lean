

theorem closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B : Set X)) ⊆ closure (interior A) := by
  -- `interior (A \ B)` is contained in `interior A`.
  have h : interior (A \ B : Set X) ⊆ interior A :=
    Topology.interior_diff_subset (A := A) (B := B)
  -- Taking closures preserves inclusions.
  exact closure_mono h