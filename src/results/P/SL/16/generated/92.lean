

theorem Topology.interior_closure_interior_inter_subset_inter_interior_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior (A ∩ B))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have h_left : x ∈ interior (closure (interior A)) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h₁ : interior (A ∩ B) ⊆ interior A :=
      interior_mono Set.inter_subset_left
    -- Taking closures preserves inclusions
    have h₂ : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
      closure_mono h₁
    -- Apply `interior_mono` to obtain the desired inclusion
    exact (interior_mono h₂) hx
  have h_right : x ∈ interior (closure (interior B)) := by
    -- `interior (A ∩ B) ⊆ interior B`
    have h₁ : interior (A ∩ B) ⊆ interior B :=
      interior_mono Set.inter_subset_right
    -- Taking closures preserves inclusions
    have h₂ : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
      closure_mono h₁
    -- Apply `interior_mono` to obtain the desired inclusion
    exact (interior_mono h₂) hx
  exact And.intro h_left h_right