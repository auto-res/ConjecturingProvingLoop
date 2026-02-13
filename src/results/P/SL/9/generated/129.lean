

theorem Topology.disjoint_closureDiff_interior {X : Type*} [TopologicalSpace X]
    {s t : Set X} :
    Disjoint (closure (s \ t)) (interior t) := by
  -- `closure (s \ t)` is contained in the complement of `interior t`.
  have hsubset : closure (s \ t) ⊆ (interior t)ᶜ := by
    intro x hx
    have hx' : x ∈ closure s \ interior t := (closure_diff_subset s t) hx
    exact hx'.2
  -- Turn this containment into the desired disjointness.
  exact
    (Set.disjoint_left).2 (by
      intro x hx_cl hx_int
      have : x ∈ (interior t)ᶜ := hsubset hx_cl
      exact this hx_int)