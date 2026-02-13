

theorem Topology.interiorClosure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (A ∩ B)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Show that `x ∈ interior (closure A)`.
  have hxA : (x : X) ∈ interior (closure A) := by
    -- Since `A ∩ B ⊆ A`, taking closures preserves the inclusion.
    have h_sub : closure (A ∩ B) ⊆ closure A := by
      have h₀ : (A ∩ B : Set X) ⊆ A := by
        intro y hy; exact hy.1
      exact closure_mono h₀
    -- Monotonicity of `interior` then gives the desired inclusion.
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure A) :=
      interior_mono h_sub
    exact h_int hx
  -- Show that `x ∈ interior (closure B)`.
  have hxB : (x : X) ∈ interior (closure B) := by
    -- Since `A ∩ B ⊆ B`, taking closures preserves the inclusion.
    have h_sub : closure (A ∩ B) ⊆ closure B := by
      have h₀ : (A ∩ B : Set X) ⊆ B := by
        intro y hy; exact hy.2
      exact closure_mono h₀
    -- Apply monotonicity of `interior` again.
    have h_int : interior (closure (A ∩ B)) ⊆ interior (closure B) :=
      interior_mono h_sub
    exact h_int hx
  exact And.intro hxA hxB