

theorem Topology.closure_interior_inter_subset_closure_inter_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A ∩ interior B) := by
  -- First, observe that `interior (A ∩ B)` is contained in `interior A ∩ interior B`.
  have h_subset : interior (A ∩ B) ⊆ interior A ∩ interior B := by
    intro x hx
    have hxA : x ∈ interior A :=
      (interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)) hx
    have hxB : x ∈ interior B :=
      (interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)) hx
    exact And.intro hxA hxB
  -- Taking closures preserves inclusions, giving the desired result.
  exact closure_mono h_subset