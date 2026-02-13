

theorem Topology.interior_inter_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  have hxA : x ∈ interior A :=
    (interior_mono Set.inter_subset_left) hx
  have hxB : x ∈ interior B :=
    (interior_mono Set.inter_subset_right) hx
  exact And.intro hxA hxB