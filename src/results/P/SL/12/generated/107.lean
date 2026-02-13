

theorem Topology.interior_closure_inter_closure_subset_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior ((closure A) ∩ (closure B) : Set X) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- Membership in `interior (closure A)`
  have hxA : x ∈ interior (closure A) := by
    -- `closure A ∩ closure B ⊆ closure A`
    have h₁ : (closure A ∩ closure B : Set X) ⊆ closure A :=
      Set.inter_subset_left
    -- Monotonicity of `interior`
    have h₂ :
        interior (closure A ∩ closure B : Set X) ⊆ interior (closure A) :=
      interior_mono h₁
    exact h₂ hx
  -- Membership in `interior (closure B)`
  have hxB : x ∈ interior (closure B) := by
    -- `closure A ∩ closure B ⊆ closure B`
    have h₁ : (closure A ∩ closure B : Set X) ⊆ closure B :=
      Set.inter_subset_right
    -- Monotonicity of `interior`
    have h₂ :
        interior (closure A ∩ closure B : Set X) ⊆ interior (closure B) :=
      interior_mono h₁
    exact h₂ hx
  exact And.intro hxA hxB