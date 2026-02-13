

theorem Topology.closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆ closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have h_subsetA : interior (A ∩ B) ⊆ interior A :=
    interior_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)
  have h_subsetB : interior (A ∩ B) ⊆ interior B :=
    interior_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)
  have hxA : x ∈ closure (interior A) :=
    (closure_mono h_subsetA) hx
  have hxB : x ∈ closure (interior B) :=
    (closure_mono h_subsetB) hx
  exact And.intro hxA hxB