

theorem Topology.closure_inter_subset_inter_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B) ⊆ closure A ∩ closure B := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ B) ⊆ A)) hx
  have hxB : x ∈ closure B :=
    (closure_mono (Set.inter_subset_right : (A ∩ B) ⊆ B)) hx
  exact And.intro hxA hxB