

theorem Topology.closure_union_eq_univ_of_dense_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Dense (A : Set X) → closure (A ∪ B : Set X) = (Set.univ : Set X) := by
  intro hDense
  -- We prove the equality by mutual inclusion.
  apply Set.Subset.antisymm
  · -- `closure (A ∪ B) ⊆ univ` is trivial.
    intro _ _
    simp
  · -- For the reverse inclusion, start with an arbitrary point `x : X`.
    intro x _
    -- Density gives `x ∈ closure A = univ`.
    have hxClA : (x : X) ∈ closure (A : Set X) := by
      simpa [hDense.closure_eq] using (by
        have : x ∈ (Set.univ : Set X) := by simp
        simpa using this)
    -- Since `A ⊆ A ∪ B`, monotonicity of `closure` yields the goal.
    have hIncl : closure (A : Set X) ⊆ closure (A ∪ B : Set X) := by
      have hSub : (A : Set X) ⊆ A ∪ B := by
        intro y hy
        exact Or.inl hy
      exact closure_mono hSub
    exact hIncl hxClA