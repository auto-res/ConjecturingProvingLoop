

theorem interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- `closure (A ∩ B)` is contained in both `closure A` and `closure B`
  have hA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  -- hence their interiors enjoy the same inclusion
  have hIntA : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono hA
  have hIntB : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono hB
  exact ⟨hIntA hx, hIntB hx⟩