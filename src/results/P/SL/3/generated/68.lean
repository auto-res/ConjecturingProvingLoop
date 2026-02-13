

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  have hxA : (x : X) ∈ interior (closure (A : Set X)) := by
    have h_subset : closure ((A ∩ B) : Set X) ⊆ closure (A : Set X) := by
      apply closure_mono
      exact Set.inter_subset_left
    exact (interior_mono h_subset) hx
  have hxB : (x : X) ∈ interior (closure (B : Set X)) := by
    have h_subset : closure ((A ∩ B) : Set X) ⊆ closure (B : Set X) := by
      apply closure_mono
      exact Set.inter_subset_right
    exact (interior_mono h_subset) hx
  exact And.intro hxA hxB