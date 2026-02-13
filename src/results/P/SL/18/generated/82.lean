

theorem interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- The closure of `A ∩ B` is contained in the closure of `A`.
  have hA : interior (closure (A ∩ B : Set X)) ⊆ interior (closure A) :=
    interior_mono (closure_mono (Set.inter_subset_left))
  -- The closure of `A ∩ B` is contained in the closure of `B`.
  have hB : interior (closure (A ∩ B : Set X)) ⊆ interior (closure B) :=
    interior_mono (closure_mono (Set.inter_subset_right))
  exact ⟨hA hx, hB hx⟩