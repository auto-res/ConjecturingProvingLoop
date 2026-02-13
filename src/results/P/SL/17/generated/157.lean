

theorem Topology.interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B) ⊆ interior A ∩ interior B := by
  intro x hx
  have hA : x ∈ interior A := by
    have hsubset : (A ∩ B) ⊆ A := Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior B := by
    have hsubset : (A ∩ B) ⊆ B := Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact And.intro hA hB