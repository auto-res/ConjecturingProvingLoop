

theorem interior_closure_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A : Set X) ∩ closure (B : Set X)) ⊆
      interior (closure (A : Set X)) ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- `interior` is monotone with respect to set inclusion.
  have hA :
      interior (closure (A : Set X) ∩ closure (B : Set X))
        ⊆ interior (closure (A : Set X)) := by
    apply interior_mono
    exact Set.inter_subset_left
  have hB :
      interior (closure (A : Set X) ∩ closure (B : Set X))
        ⊆ interior (closure (B : Set X)) := by
    apply interior_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩