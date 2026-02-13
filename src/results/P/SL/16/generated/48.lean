

theorem Topology.interior_closure_inter_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A := by
      apply closure_mono
      exact Set.inter_subset_left
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B := by
      apply closure_mono
      exact Set.inter_subset_right
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB