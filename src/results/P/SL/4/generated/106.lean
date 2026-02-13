

theorem closure_interior_inter_subset_closure_inter_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- The interior of `A ∩ B` is contained in both `interior A` and `interior B`.
  have h :
      interior (A ∩ B) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono Set.inter_subset_left) hx
    have hxB : x ∈ interior B :=
      (interior_mono Set.inter_subset_right) hx
    exact And.intro hxA hxB
  -- Taking closures preserves inclusions.
  exact closure_mono h