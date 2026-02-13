

theorem Topology.interiorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := by
    have h_subset : closure (A ∩ B) ⊆ closure A := by
      have h_sub : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h_sub
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure B) := by
    have h_subset : closure (A ∩ B) ⊆ closure B := by
      have h_sub : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact closure_mono h_sub
    exact (interior_mono h_subset) hx
  exact ⟨hxA, hxB⟩