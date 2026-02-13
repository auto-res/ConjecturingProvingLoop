

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hxA : x ∈ interior (closure (interior A)) := by
    have h_subset : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
      have h_int_subset : interior (A ∩ B : Set X) ⊆ interior A := by
        have h_set : (A ∩ B : Set X) ⊆ A := by
          intro y hy; exact hy.1
        exact interior_mono h_set
      exact closure_mono h_int_subset
    exact (interior_mono h_subset) hx
  have hxB : x ∈ interior (closure (interior B)) := by
    have h_subset : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
      have h_int_subset : interior (A ∩ B : Set X) ⊆ interior B := by
        have h_set : (A ∩ B : Set X) ⊆ B := by
          intro y hy; exact hy.2
        exact interior_mono h_set
      exact closure_mono h_int_subset
    exact (interior_mono h_subset) hx
  exact ⟨hxA, hxB⟩