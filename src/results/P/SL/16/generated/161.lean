

theorem Topology.interior_closure_inter_closure_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B : Set X) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First inclusion: `closure A ∩ closure B ⊆ closure A`.
  have hxA : x ∈ interior (closure A) := by
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure A := by
      intro y hy; exact hy.1
    exact (interior_mono h_subset) hx
  -- Second inclusion: `closure A ∩ closure B ⊆ closure B`.
  have hxB : x ∈ interior (closure B) := by
    have h_subset : (closure A ∩ closure B : Set X) ⊆ closure B := by
      intro y hy; exact hy.2
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB