

theorem Topology.P1_union_left_denseInterior {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h_dense : closure (interior A) = (Set.univ : Set X)) :
    Topology.P1 (X := X) (A ∪ B) := by
  dsimp [Topology.P1]
  intro x hxUnion
  -- Every point of `X` lies in `closure (interior A)` by the density hypothesis.
  have hxClosureIntA : x ∈ closure (interior A) := by
    have : (x : X) ∈ (Set.univ : Set X) := by simp
    simpa [h_dense] using this
  -- Monotonicity of `closure ∘ interior` gives the required inclusion.
  have h_subset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
    apply closure_mono
    have h_int_subset : interior A ⊆ interior (A ∪ B) := by
      have h_sub : A ⊆ A ∪ B := by
        intro y hy; exact Or.inl hy
      exact interior_mono h_sub
    exact h_int_subset
  exact h_subset hxClosureIntA