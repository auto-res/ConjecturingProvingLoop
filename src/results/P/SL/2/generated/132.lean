

theorem Topology.closure_interior_union_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∪ closure (interior (B : Set X)) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- `x ∈ closure (interior A)`; transport along the inclusions
      have hsubset :
          closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) := by
        -- first relate the interiors
        have hInt : (interior (A : Set X)) ⊆ interior (A ∪ B) := by
          have hSub : (A : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inl hy
          exact interior_mono hSub
        -- taking closures preserves inclusion
        exact closure_mono hInt
      exact hsubset hxA
  | inr hxB =>
      -- symmetric argument for the second summand
      have hsubset :
          closure (interior (B : Set X)) ⊆ closure (interior (A ∪ B)) := by
        have hInt : (interior (B : Set X)) ⊆ interior (A ∪ B) := by
          have hSub : (B : Set X) ⊆ A ∪ B := by
            intro y hy
            exact Or.inr hy
          exact interior_mono hSub
        exact closure_mono hInt
      exact hsubset hxB