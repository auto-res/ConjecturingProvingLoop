

theorem Topology.interior_subset_interior_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior A ⊆ interior (closure (A ∪ B)) := by
  intro x hx
  -- First, note that `A ⊆ closure (A ∪ B)`.
  have hSub : (A : Set X) ⊆ closure (A ∪ B) := by
    intro y hy
    -- `y ∈ A` implies `y ∈ A ∪ B`.
    have : (y : X) ∈ (A ∪ B : Set X) := Or.inl hy
    -- The universal property of the closure yields the claim.
    exact subset_closure this
  -- Monotonicity of `interior ∘ closure` gives the desired inclusion.
  exact (interior_mono hSub) hx