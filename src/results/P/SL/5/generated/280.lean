

theorem closure_interior_left_inter_subset_closures {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior A ∩ B : Set X) ⊆ closure (interior A) ∩ closure B := by
  intro x hx
  have hx₁ : x ∈ closure (interior A) := by
    have hsubset : (interior A ∩ B : Set X) ⊆ interior A :=
      Set.inter_subset_left
    exact (closure_mono hsubset) hx
  have hx₂ : x ∈ closure B := by
    have hsubset : (interior A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    exact (closure_mono hsubset) hx
  exact ⟨hx₁, hx₂⟩