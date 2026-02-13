

theorem Topology.closure_interior_inter_subset_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show membership in `closure (interior A)`
  have hxA : x ∈ closure (interior A) := by
    -- `A ∩ B ⊆ A`
    have h_subset_AB_A : (A ∩ B : Set X) ⊆ A := Set.inter_subset_left
    -- Then `interior (A ∩ B) ⊆ interior A`
    have h_int : (interior (A ∩ B : Set X) : Set X) ⊆ interior A :=
      interior_mono h_subset_AB_A
    -- Taking closures preserves inclusion
    have h_closure : closure (interior (A ∩ B : Set X)) ⊆ closure (interior A) :=
      closure_mono h_int
    exact h_closure hx
  -- Show membership in `closure (interior B)`
  have hxB : x ∈ closure (interior B) := by
    -- `A ∩ B ⊆ B`
    have h_subset_AB_B : (A ∩ B : Set X) ⊆ B := Set.inter_subset_right
    -- Then `interior (A ∩ B) ⊆ interior B`
    have h_int : (interior (A ∩ B : Set X) : Set X) ⊆ interior B :=
      interior_mono h_subset_AB_B
    -- Taking closures preserves inclusion
    have h_closure : closure (interior (A ∩ B : Set X)) ⊆ closure (interior B) :=
      closure_mono h_int
    exact h_closure hx
  exact And.intro hxA hxB