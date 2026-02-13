

theorem Topology.closure_inter_interiors_subset_inter_closure_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure ((interior (A : Set X)) ∩ interior B) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  have hxA : x ∈ closure (interior A) :=
    (closure_mono
        (Set.inter_subset_left :
          (interior (A : Set X) ∩ interior B : Set X) ⊆ interior A)) hx
  have hxB : x ∈ closure (interior B) :=
    (closure_mono
        (Set.inter_subset_right :
          (interior (A : Set X) ∩ interior B : Set X) ⊆ interior B)) hx
  exact ⟨hxA, hxB⟩