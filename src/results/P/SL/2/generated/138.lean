

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior ((A ∩ B) : Set X)) ⊆
      closure (interior (A : Set X)) ∩ closure (interior (B : Set X)) := by
  intro x hx
  -- Membership in the left component
  have hxA : x ∈ closure (interior (A : Set X)) := by
    -- `interior (A ∩ B)` is contained in `interior A`
    have hIntSub : (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (A : Set X) := by
      have : ((A ∩ B) : Set X) ⊆ A := by
        intro y hy
        exact hy.1
      exact interior_mono this
    -- Taking closures preserves inclusions
    exact (closure_mono hIntSub) hx
  -- Membership in the right component
  have hxB : x ∈ closure (interior (B : Set X)) := by
    -- `interior (A ∩ B)` is contained in `interior B`
    have hIntSub : (interior ((A ∩ B) : Set X) : Set X) ⊆ interior (B : Set X) := by
      have : ((A ∩ B) : Set X) ⊆ B := by
        intro y hy
        exact hy.2
      exact interior_mono this
    -- Taking closures preserves inclusions
    exact (closure_mono hIntSub) hx
  exact And.intro hxA hxB