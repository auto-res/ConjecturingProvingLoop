

theorem Topology.interior_intersection_subset_inter_interior {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior ((A ∩ B) : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  -- `A ∩ B ⊆ A`, hence `interior (A ∩ B) ⊆ interior A`.
  have hxA : (x : X) ∈ interior A :=
    (interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  -- Similarly, `A ∩ B ⊆ B`, so `interior (A ∩ B) ⊆ interior B`.
  have hxB : (x : X) ∈ interior B :=
    (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hxA, hxB⟩