

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have hsubset : closure (A ∩ B) ⊆ closure A :=
      closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact (interior_mono hsubset) hx
  have hB : x ∈ interior (closure B) := by
    have hsubset : closure (A ∩ B) ⊆ closure B :=
      closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact (interior_mono hsubset) hx
  exact ⟨hA, hB⟩