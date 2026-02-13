

theorem Topology.closure_interior_union_subset_closure_interior
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior A ∪ interior B : Set X) ⊆
      closure (interior (A ∪ B)) := by
  -- First, show that `interior A ∪ interior B` is contained in `interior (A ∪ B)`.
  have hsubset : (interior A ∪ interior B : Set X) ⊆ interior (A ∪ B) := by
    intro x hx
    cases hx with
    | inl hA =>
        have hA' : interior A ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inl hy
        exact hA' hA
    | inr hB =>
        have hB' : interior B ⊆ interior (A ∪ B) := by
          apply interior_mono
          intro y hy
          exact Or.inr hy
        exact hB' hB
  -- Taking closures preserves inclusions.
  exact closure_mono hsubset