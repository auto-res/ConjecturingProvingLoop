

theorem Topology.closure_interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A \ B)) ⊆ closure (interior A) := by
  -- Since `A \ B ⊆ A`, the same inclusion holds for their interiors.
  have hsubset : interior (A \ B) ⊆ interior A := by
    have hAB : (A \ B : Set X) ⊆ A := by
      intro x hx
      exact hx.1
    exact interior_mono hAB
  -- Taking closures preserves set inclusion.
  exact closure_mono hsubset