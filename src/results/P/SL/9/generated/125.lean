

theorem Topology.disjoint_closureCompl_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Disjoint (closure (Aᶜ)) (interior A) := by
  -- `closure (Aᶜ)` is contained in the complement of `interior A`.
  have hsubset : closure (Aᶜ) ⊆ (interior A)ᶜ :=
    Topology.closure_compl_subset_compl_interior (A := A)
  -- Translate this containment into disjointness.
  exact (Set.disjoint_left).2 (by
    intro x hx_cl hx_int
    have : x ∈ (interior A)ᶜ := hsubset hx_cl
    exact this hx_int)