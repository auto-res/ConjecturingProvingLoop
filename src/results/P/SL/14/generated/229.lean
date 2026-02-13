

theorem Topology.interiorClosureInterior_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  -- Show `x ∈ interior (closure (interior A))`
  have hxA : (x : X) ∈ interior (closure (interior A)) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h_int_subset : interior (A ∩ B : Set X) ⊆ interior A :=
      interior_mono (by
        intro y hy
        exact hy.1)
    -- Hence `closure (interior (A ∩ B)) ⊆ closure (interior A)`
    have h_closure_subset :
        closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h_int_subset
    -- Taking interiors preserves the inclusion
    have h_interior_subset :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior A)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  -- Show `x ∈ interior (closure (interior B))`
  have hxB : (x : X) ∈ interior (closure (interior B)) := by
    -- `interior (A ∩ B) ⊆ interior B`
    have h_int_subset : interior (A ∩ B : Set X) ⊆ interior B :=
      interior_mono (by
        intro y hy
        exact hy.2)
    -- Hence `closure (interior (A ∩ B)) ⊆ closure (interior B)`
    have h_closure_subset :
        closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int_subset
    -- Taking interiors preserves the inclusion
    have h_interior_subset :
        interior (closure (interior (A ∩ B))) ⊆
          interior (closure (interior B)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  exact And.intro hxA hxB