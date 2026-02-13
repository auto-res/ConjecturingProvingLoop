

theorem Topology.closure_inter_interior_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure A ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure A :=
    (closure_mono (Set.inter_subset_left : (A ∩ interior B) ⊆ A)) hx
  have hxIntB : x ∈ closure (interior B) :=
    (closure_mono (Set.inter_subset_right : (A ∩ interior B) ⊆ interior B)) hx
  exact And.intro hxA hxIntB