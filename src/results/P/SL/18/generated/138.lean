

theorem interior_closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B : Set X))) ⊆
      interior (closure (interior A)) ∩
        interior (closure (interior B)) := by
  intro x hx
  have hA :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior A)) := by
    apply interior_mono
    have hSub_int : interior (A ∩ B : Set X) ⊆ interior A := by
      apply interior_mono
      exact Set.inter_subset_left
    exact closure_mono hSub_int
  have hB :
      interior (closure (interior (A ∩ B : Set X))) ⊆
        interior (closure (interior B)) := by
    apply interior_mono
    have hSub_int : interior (A ∩ B : Set X) ⊆ interior B := by
      apply interior_mono
      exact Set.inter_subset_right
    exact closure_mono hSub_int
  exact ⟨hA hx, hB hx⟩