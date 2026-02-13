

theorem Topology.closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hA =>
      -- Handle the case `x ∈ closure (interior A)`.
      have h_sub : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        -- Since `A ⊆ A ∪ B`, their interiors satisfy the same inclusion.
        have h_int : (interior A : Set X) ⊆ interior (A ∪ B) := by
          have : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono this
        -- Taking closures preserves the inclusion.
        exact closure_mono h_int
      exact h_sub hA
  | inr hB =>
      -- Symmetric argument for the case `x ∈ closure (interior B)`.
      have h_sub : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have h_int : (interior B : Set X) ⊆ interior (A ∪ B) := by
          have : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono this
        exact closure_mono h_int
      exact h_sub hB