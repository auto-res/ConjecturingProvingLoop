

theorem closure_inter_subset_closure_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hA, hB⟩