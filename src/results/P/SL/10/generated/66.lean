

theorem Topology.interior_closure_inter_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆ interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show `closure (A ∩ B)` is contained in each closure separately.
  have h_closureA : closure (A ∩ B) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have h_closureB : closure (A ∩ B) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  -- Pass to interiors via monotonicity.
  have hxA : x ∈ interior (closure A) := (interior_mono h_closureA) hx
  have hxB : x ∈ interior (closure B) := (interior_mono h_closureB) hx
  exact And.intro hxA hxB