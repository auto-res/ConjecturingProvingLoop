

theorem Topology.interior_diff_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A \ B : Set X) ⊆ interior A := by
  -- The set `A \ B` is contained in `A`.
  exact interior_mono (by
    intro x hx
    exact hx.1)