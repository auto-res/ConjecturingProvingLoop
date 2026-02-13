

theorem interior_closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hA : (closure (A ∩ B) : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : (closure (A ∩ B) : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  exact ⟨(interior_mono hA) hx, (interior_mono hB) hx⟩