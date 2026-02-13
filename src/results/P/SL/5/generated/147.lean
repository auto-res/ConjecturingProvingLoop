

theorem closure_eq_univ_of_closure_interior_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} (h : closure (interior (A : Set X)) = (Set.univ : Set X)) :
    closure (A : Set X) = (Set.univ : Set X) := by
  -- Prove the inclusion `closure A ⊆ univ`, which is trivial.
  have h₁ : closure (A : Set X) ⊆ (Set.univ : Set X) := by
    intro _ _
    trivial
  -- Prove the reverse inclusion `univ ⊆ closure A`.
  have h₂ : (Set.univ : Set X) ⊆ closure (A : Set X) := by
    intro x _
    -- Since `closure (interior A) = univ`, every `x` belongs to it.
    have hxInt : x ∈ closure (interior (A : Set X)) := by
      have : x ∈ (Set.univ : Set X) := by
        trivial
      simpa [h] using this
    -- Use monotonicity of `closure` to deduce `x ∈ closure A`.
    have hsubset : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      Topology.closure_interior_subset_closure (X := X) A
    exact hsubset hxInt
  exact le_antisymm h₁ h₂