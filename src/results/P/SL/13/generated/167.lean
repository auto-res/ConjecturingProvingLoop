

theorem Topology.interior_closure_interior_inter_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- First direction: relate to `A`.
  have h_subsetA :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
    have h_intA :
        interior ((A ∩ B) : Set X) ⊆ interior A :=
      interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
    exact closure_mono h_intA
  have hxA : x ∈ interior (closure (interior A)) :=
    (interior_mono h_subsetA) hx
  -- Second direction: relate to `B`.
  have h_subsetB :
      closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
    have h_intB :
        interior ((A ∩ B) : Set X) ⊆ interior B :=
      interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
    exact closure_mono h_intB
  have hxB : x ∈ interior (closure (interior B)) :=
    (interior_mono h_subsetB) hx
  exact ⟨hxA, hxB⟩