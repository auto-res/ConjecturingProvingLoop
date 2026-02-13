

theorem Topology.frontier_symmDiff_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    frontier ((A \ B) ∪ (B \ A)) ⊆ frontier A ∪ frontier B := by
  -- First, use the union lemma for the frontier.
  have h₁ :
      frontier ((A \ B) ∪ (B \ A)) ⊆
        frontier (A \ B) ∪ frontier (B \ A) :=
    Topology.frontier_union_subset (A := A \ B) (B := B \ A)
  -- Next, control each summand with the corresponding difference lemma.
  have h₂ : frontier (A \ B) ⊆ frontier A ∪ frontier B :=
    Topology.frontier_diff_subset (A := A) (B := B)
  have h₃ : frontier (B \ A) ⊆ frontier A ∪ frontier B := by
    -- Swap the roles of `A` and `B` in the previous lemma.
    simpa [Set.union_comm] using
      (Topology.frontier_diff_subset (A := B) (B := A))
  -- Assemble the three inclusions.
  intro x hx
  have hx' : x ∈ frontier (A \ B) ∪ frontier (B \ A) := h₁ hx
  cases hx' with
  | inl hA =>
      exact h₂ hA
  | inr hB =>
      exact h₃ hB