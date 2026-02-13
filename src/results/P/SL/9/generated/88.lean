

theorem Topology.closureInterior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    closure (interior (A ∩ B)) ⊆
      closure (interior A) ∩ closure (interior B) := by
  intro x hx
  -- Show `x ∈ closure (interior A)`.
  have hxA : x ∈ closure (interior A) := by
    -- `interior (A ∩ B) ⊆ interior A`
    have h_subset : interior (A ∩ B : Set X) ⊆ interior A := by
      -- Since `A ∩ B ⊆ A`, apply monotonicity of `interior`.
      have h_set : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact interior_mono h_set
    -- Taking closures preserves inclusion.
    have h_closure : closure (interior (A ∩ B)) ⊆ closure (interior A) :=
      closure_mono h_subset
    exact h_closure hx
  -- Show `x ∈ closure (interior B)`.
  have hxB : x ∈ closure (interior B) := by
    have h_subset : interior (A ∩ B : Set X) ⊆ interior B := by
      have h_set : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact interior_mono h_set
    have h_closure : closure (interior (A ∩ B)) ⊆ closure (interior B) :=
      closure_mono h_subset
    exact h_closure hx
  exact ⟨hxA, hxB⟩