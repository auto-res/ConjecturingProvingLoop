

theorem Topology.interiorClosure_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show membership in `interior (closure A)`
  have hLeft : x ∈ interior (closure A) := by
    have hSub : interior (closure (A ∩ B)) ⊆ interior (closure A) := by
      apply interior_mono
      have : closure (A ∩ B) ⊆ closure A := by
        apply closure_mono
        exact Set.inter_subset_left
      exact this
    exact hSub hx
  -- Show membership in `interior (closure B)`
  have hRight : x ∈ interior (closure B) := by
    have hSub : interior (closure (A ∩ B)) ⊆ interior (closure B) := by
      apply interior_mono
      have : closure (A ∩ B) ⊆ closure B := by
        apply closure_mono
        exact Set.inter_subset_right
      exact this
    exact hSub hx
  exact ⟨hLeft, hRight⟩