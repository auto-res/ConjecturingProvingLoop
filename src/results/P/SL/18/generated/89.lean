

theorem closure_interior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hLeft :
      closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) := by
    apply closure_mono
    have : interior (A ∩ B : Set X) ⊆ interior A := by
      apply interior_mono
      exact Set.inter_subset_left
    exact this
  have hRight :
      closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) := by
    apply closure_mono
    have : interior (A ∩ B : Set X) ⊆ interior B := by
      apply interior_mono
      exact Set.inter_subset_right
    exact this
  exact ⟨hLeft hx, hRight hx⟩