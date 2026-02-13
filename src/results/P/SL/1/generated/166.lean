

theorem Topology.interior_closure_interior_union_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure (interior A)) ∪ interior (closure (interior B)) ⊆
      interior (closure (interior (A ∪ B))) := by
  intro x hx
  cases hx with
  | inl hxA =>
      -- Handle the case `x ∈ interior (closure (interior A))`.
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        -- Show `closure (interior A) ⊆ closure (interior (A ∪ B))`.
        have hcl : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          -- Show `interior A ⊆ interior (A ∪ B)`.
          have : interior A ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inl hy
          exact this
        exact hcl
      exact hsubset hxA
  | inr hxB =>
      -- Handle the case `x ∈ interior (closure (interior B))`.
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        apply interior_mono
        -- Show `closure (interior B) ⊆ closure (interior (A ∪ B))`.
        have hcl : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
          apply closure_mono
          -- Show `interior B ⊆ interior (A ∪ B)`.
          have : interior B ⊆ interior (A ∪ B) := by
            apply interior_mono
            intro y hy
            exact Or.inr hy
          exact this
        exact hcl
      exact hsubset hxB