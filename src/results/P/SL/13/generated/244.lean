

theorem Topology.closure_interior_inter_subset_inter_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ B) ⊆
      closure (interior A) ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ B` is contained in `interior A`
    have h_subset : ((interior (A : Set X)) ∩ B : Set X) ⊆ interior A := by
      intro y hy
      exact hy.1
    exact (closure_mono h_subset) hx
  have hxB : x ∈ closure B := by
    -- `interior A ∩ B` is contained in `B`
    have h_subset : ((interior (A : Set X)) ∩ B : Set X) ⊆ B := by
      intro y hy
      exact hy.2
    exact (closure_mono h_subset) hx
  exact ⟨hxA, hxB⟩