

theorem Topology.closure_interior_inter_subset_inter_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have h_int_subset_left : interior (A ∩ B) ⊆ interior A :=
    interior_mono Set.inter_subset_left
  have h_int_subset_right : interior (A ∩ B) ⊆ interior B :=
    interior_mono Set.inter_subset_right
  have hx_left : x ∈ closure (interior A) :=
    (closure_mono h_int_subset_left) hx
  have hx_right : x ∈ closure (interior B) :=
    (closure_mono h_int_subset_right) hx
  exact ⟨hx_left, hx_right⟩