

theorem interior_closure_interInterior_subset_inter_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ interior B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First, show `x ∈ interior (closure A)`.
  have hxA : x ∈ interior (closure A) := by
    -- Because `A ∩ interior B ⊆ A`, their closures are related.
    have h_sub : closure (A ∩ interior B) ⊆ closure A := by
      have h : A ∩ interior B ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h
    -- Apply monotonicity of `interior`.
    have h_int : interior (closure (A ∩ interior B)) ⊆ interior (closure A) :=
      interior_mono h_sub
    exact h_int hx
  -- Next, show `x ∈ interior (closure B)`.
  have hxB : x ∈ interior (closure B) := by
    -- Since `interior B ⊆ B`, we get another inclusion of closures.
    have h_sub : closure (A ∩ interior B) ⊆ closure B := by
      have h : A ∩ interior B ⊆ B := by
        intro y hy; exact (interior_subset : interior B ⊆ B) hy.2
      exact closure_mono h
    -- Again use monotonicity of `interior`.
    have h_int : interior (closure (A ∩ interior B)) ⊆ interior (closure B) :=
      interior_mono h_sub
    exact h_int hx
  -- Combine the two memberships.
  exact And.intro hxA hxB