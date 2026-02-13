

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in the first component.
  have hA : x ∈ closure (interior A) := by
    have hsubset : closure (interior (A ∩ B)) ⊆ closure (interior A) := by
      apply closure_mono
      exact interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact hsubset hx
  -- Show membership in the second component.
  have hB : x ∈ closure (interior B) := by
    have hsubset : closure (interior (A ∩ B)) ⊆ closure (interior B) := by
      apply closure_mono
      exact interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact hsubset hx
  exact ⟨hA, hB⟩