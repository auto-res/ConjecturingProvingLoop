

theorem closure_interior_inter_interior_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA :
      closure (interior (A : Set X) ∩ interior B) ⊆ closure (interior A) := by
    apply closure_mono
    exact Set.inter_subset_left
  have hB :
      closure (interior (A : Set X) ∩ interior B) ⊆ closure (interior B) := by
    apply closure_mono
    exact Set.inter_subset_right
  exact ⟨hA hx, hB hx⟩