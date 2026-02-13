

theorem interior_closure_inter_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubset : (closure A ∩ closure B : Set X) ⊆ closure A :=
      Set.inter_subset_left
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior (closure B) := by
    have hsubset : (closure A ∩ closure B : Set X) ⊆ closure B :=
      Set.inter_subset_right
    exact (interior_mono hsubset) hx
  exact ⟨hA, hB⟩