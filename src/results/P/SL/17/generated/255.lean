

theorem Topology.interior_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have h_sub : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono h_sub) hx
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have h_sub : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono h_sub) hx
  exact And.intro hxA hxB