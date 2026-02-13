

theorem interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have h_sub : A ∩ B ⊆ A := Set.inter_subset_left
    exact (interior_mono h_sub) hx
  have hB : x ∈ interior B := by
    have h_sub : A ∩ B ⊆ B := Set.inter_subset_right
    exact (interior_mono h_sub) hx
  exact And.intro hA hB