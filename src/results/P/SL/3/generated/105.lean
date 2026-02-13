

theorem interior_inter_subset_interiors {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆
      interior (A : Set X) ∩ interior (B : Set X) := by
  intro x hx
  have hxA : (x : X) ∈ interior (A : Set X) := by
    have hSubset : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    exact (interior_mono hSubset) hx
  have hxB : (x : X) ∈ interior (B : Set X) := by
    have hSubset : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (interior_mono hSubset) hx
  exact And.intro hxA hxB