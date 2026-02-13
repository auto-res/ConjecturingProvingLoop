

theorem interior_closure_inter_subset_interior_closure_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A ∩ closure B) := by
  -- First, show the underlying inclusion for the closed sets themselves.
  have h_subset : closure (A ∩ B) ⊆ closure A ∩ closure B := by
    intro x hx
    have hxA : x ∈ closure A :=
      (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
    have hxB : x ∈ closure B :=
      (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Taking interiors preserves inclusions.
  exact interior_mono h_subset