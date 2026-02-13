

theorem Topology.frontier_union_three_subset_union_frontier
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    frontier (A ∪ B ∪ C : Set X) ⊆ frontier A ∪ frontier B ∪ frontier C := by
  intro x hx
  -- Reassociate the union to use the two–set lemma twice.
  have hx₁ : x ∈ frontier ((A ∪ B) ∪ C : Set X) := by
    simpa [Set.union_assoc] using hx
  -- First application: break the frontier of `(A ∪ B) ∪ C`.
  have h₁ : x ∈ frontier (A ∪ B) ∪ frontier C :=
    (frontier_union_subset (A := A ∪ B) (B := C)) hx₁
  cases h₁ with
  | inl hAB =>
      -- Second application: break the frontier of `A ∪ B`.
      have h₂ : x ∈ frontier A ∪ frontier B :=
        (frontier_union_subset (A := A) (B := B)) hAB
      cases h₂ with
      | inl hA =>
          -- `x ∈ frontier A`
          exact Or.inl (Or.inl hA)
      | inr hB =>
          -- `x ∈ frontier B`
          exact Or.inl (Or.inr hB)
  | inr hC =>
      -- `x ∈ frontier C`
      exact Or.inr hC