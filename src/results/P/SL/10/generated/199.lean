

theorem Topology.interior_closure_inter_closure_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A ∩ closure B) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  have hxA : x ∈ interior (closure A) :=
    (interior_mono
        (Set.inter_subset_left : (closure A ∩ closure B) ⊆ closure A)) hx
  have hxB : x ∈ interior (closure B) :=
    (interior_mono
        (Set.inter_subset_right : (closure A ∩ closure B) ⊆ closure B)) hx
  exact And.intro hxA hxB