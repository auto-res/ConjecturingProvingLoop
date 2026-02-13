

theorem Topology.interior_inter_closure_subset_inter_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ closure (B : Set X) : Set X) ⊆
      interior A ∩ interior (closure B) := by
  intro x hx
  -- `x` lies in `interior A`
  have hxA : x ∈ interior A := by
    -- `A ∩ closure B ⊆ A`
    have h₁ : (A ∩ closure (B : Set X) : Set X) ⊆ A :=
      Set.inter_subset_left
    -- Monotonicity of `interior`
    have h₂ :
        interior (A ∩ closure (B : Set X) : Set X) ⊆ interior A :=
      interior_mono h₁
    exact h₂ hx
  -- `x` lies in `interior (closure B)`
  have hxB : x ∈ interior (closure B) := by
    -- `A ∩ closure B ⊆ closure B`
    have h₁ : (A ∩ closure (B : Set X) : Set X) ⊆ closure B :=
      Set.inter_subset_right
    -- Monotonicity of `interior`
    have h₂ :
        interior (A ∩ closure (B : Set X) : Set X) ⊆
          interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB