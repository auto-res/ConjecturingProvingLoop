

theorem interior_closure_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : x ∈ interior (closure A) := by
    have h_subset : interior (closure (A ∩ B)) ⊆ interior (closure A) := by
      have h_closure : closure (A ∩ B) ⊆ closure A :=
        closure_mono (Set.inter_subset_left)
      exact interior_mono h_closure
    exact h_subset hx
  have hB : x ∈ interior (closure B) := by
    have h_subset : interior (closure (A ∩ B)) ⊆ interior (closure B) := by
      have h_closure : closure (A ∩ B) ⊆ closure B :=
        closure_mono (Set.inter_subset_right)
      exact interior_mono h_closure
    exact h_subset hx
  exact And.intro hA hB