

theorem interior_inter_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure (B : Set X) : Set X) ⊆
      interior A ∩ interior (closure (B : Set X)) := by
  intro x hx
  -- Inclusion into `interior A`.
  have hA :
      interior (A ∩ closure (B : Set X) : Set X) ⊆ interior A := by
    apply interior_mono
    exact Set.inter_subset_left
  -- Inclusion into `interior (closure B)`.
  have hB :
      interior (A ∩ closure (B : Set X) : Set X) ⊆
        interior (closure (B : Set X)) := by
    apply interior_mono
    intro y hy
    exact hy.2
  exact ⟨hA hx, hB hx⟩