

theorem interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A := by
    have hsubset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hxB : x ∈ interior B := by
    have hsubset : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact ⟨hxA, hxB⟩