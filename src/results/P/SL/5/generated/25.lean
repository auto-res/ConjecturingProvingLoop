

theorem closure_interior_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hA : (interior (A ∩ B) : Set X) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : (interior (A ∩ B) : Set X) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨(closure_mono hA) hx, (closure_mono hB) hx⟩