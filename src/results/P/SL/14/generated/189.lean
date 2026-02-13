

theorem Topology.closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure A ∩ closure B := by
  intro x hx
  -- Show `x ∈ closure A`.
  have hxA : (x : X) ∈ closure A := by
    -- `A ∩ B ⊆ A`
    have h_subset : (A ∩ B : Set X) ⊆ A := by
      intro y hy; exact hy.1
    -- Taking closures preserves the inclusion.
    have h_closure : closure (A ∩ B : Set X) ⊆ closure A :=
      closure_mono h_subset
    exact h_closure hx
  -- Show `x ∈ closure B`.
  have hxB : (x : X) ∈ closure B := by
    -- `A ∩ B ⊆ B`
    have h_subset : (A ∩ B : Set X) ⊆ B := by
      intro y hy; exact hy.2
    -- Taking closures preserves the inclusion.
    have h_closure : closure (A ∩ B : Set X) ⊆ closure B :=
      closure_mono h_subset
    exact h_closure hx
  exact And.intro hxA hxB