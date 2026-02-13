

theorem closure_interior_inter_subset_closure_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A ∩ interior B) := by
  -- First, relate the two interiors directly.
  have hSub :
      interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact ⟨hxA, hxB⟩
  -- Taking closures preserves inclusions.
  exact closure_mono hSub