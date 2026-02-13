

theorem Topology.closure_interior_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ closure B) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  -- `interior A ∩ closure B` is contained in `interior A`.
  have hx_left : x ∈ closure (interior A) := by
    have h_subset_left : interior A ∩ closure B ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono h_subset_left) hx
  -- Likewise, `interior A ∩ closure B` is contained in `closure B`.
  have hx_right : x ∈ closure B := by
    have h_subset_right : interior A ∩ closure B ⊆ closure B := by
      intro y hy
      exact hy.2
    have : closure (interior A ∩ closure B) ⊆ closure (closure B) :=
      closure_mono h_subset_right
    simpa [closure_closure] using this hx
  exact And.intro hx_left hx_right