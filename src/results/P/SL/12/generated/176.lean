

theorem Topology.closure_interior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ∪ closure (interior C) ⊆
      closure (interior (A ∪ B ∪ C : Set X)) := by
  -- Each individual term of the left‐hand side is contained in the right‐hand side.
  have hA :
      closure (interior (A : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ A ⊆ A ∪ B ∪ C`
    exact Or.inl (Or.inl hx)
  have hB :
      closure (interior (B : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ B ⊆ A ∪ B ⊆ (A ∪ B) ∪ C`
    exact Or.inl (Or.inr hx)
  have hC :
      closure (interior (C : Set X)) ⊆
        closure (interior (A ∪ B ∪ C : Set X)) := by
    apply Topology.closure_interior_mono
    intro x hx
    -- `x ∈ C ⊆ (A ∪ B) ∪ C`
    exact Or.inr hx
  -- Analyse membership in the triple union.
  intro x hx
  cases hx with
  | inl hxAB =>
      cases hxAB with
      | inl hxA => exact hA hxA
      | inr hxB => exact hB hxB
  | inr hxC => exact hC hxC