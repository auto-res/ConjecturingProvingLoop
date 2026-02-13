

theorem Topology.interior_subset_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    (interior (A : Set X)) ⊆ interior (A ∪ B) := by
  intro x hx
  -- Since `A ⊆ A ∪ B`, monotonicity of `interior` yields the claim.
  have hSub : (A : Set X) ⊆ A ∪ B := by
    intro y hy
    exact Or.inl hy
  exact (interior_mono hSub) hx