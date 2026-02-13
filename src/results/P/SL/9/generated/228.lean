

theorem Topology.boundary_union_three_subset_union_boundary
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    closure (A ∪ B ∪ C) \ interior (A ∪ B ∪ C) ⊆
      (closure A \ interior A) ∪ (closure B \ interior B) ∪
        (closure C \ interior C) := by
  intro x hx
  -- First, treat the union as `((A ∪ B) ∪ C)` and apply the two‐set lemma.
  have h₁ :
      x ∈ (closure (A ∪ B) \ interior (A ∪ B)) ∪
          (closure C \ interior C) :=
    (Topology.boundary_union_subset_union_boundary
        (A := A ∪ B) (B := C)) hx
  cases h₁ with
  | inl hAB =>
      -- Now decompose the boundary of `A ∪ B`.
      have h₂ :
          x ∈ (closure A \ interior A) ∪ (closure B \ interior B) :=
        (Topology.boundary_union_subset_union_boundary
            (A := A) (B := B)) hAB
      cases h₂ with
      | inl hA =>
          exact Or.inl (Or.inl hA)
      | inr hB =>
          exact Or.inl (Or.inr hB)
  | inr hC =>
      exact Or.inr hC