

theorem interior_closure_left_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior ((closure (A : Set X)) ∩ B) ⊆
      interior (closure A) ∩ interior B := by
  intro x hx
  have hx₁ : x ∈ interior (closure A) :=
    (interior_mono
      (Set.inter_subset_left :
        ((closure (A : Set X)) ∩ B) ⊆ closure A)) hx
  have hx₂ : x ∈ interior B :=
    (interior_mono
      (Set.inter_subset_right :
        ((closure (A : Set X)) ∩ B) ⊆ B)) hx
  exact ⟨hx₁, hx₂⟩