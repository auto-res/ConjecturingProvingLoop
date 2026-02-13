

theorem closure_interInterior_inter_subset_inter_closureInterior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) := by
    -- `interior A ∩ interior B` is contained in `interior A`.
    have h : interior A ∩ interior B ⊆ interior A := by
      intro y hy; exact hy.1
    exact (closure_mono h) hx
  have hxB : x ∈ closure (interior B) := by
    -- `interior A ∩ interior B` is contained in `interior B`.
    have h : interior A ∩ interior B ⊆ interior B := by
      intro y hy; exact hy.2
    exact (closure_mono h) hx
  exact And.intro hxA hxB