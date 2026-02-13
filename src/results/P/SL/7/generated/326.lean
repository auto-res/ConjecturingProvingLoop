

theorem Topology.interiorClosureInterior_union_three_subset
    {X : Type*} [TopologicalSpace X] {A B C : Set X} :
    interior (closure (interior A)) ∪
        interior (closure (interior B)) ∪
        interior (closure (interior C)) ⊆
      interior (closure (interior (A ∪ B ∪ C))) := by
  intro x hx
  -- Split the membership in the three‐fold union
  cases hx with
  | inl hAB =>
      cases hAB with
      | inl hA =>
          -- Handle the case `x ∈ interior (closure (interior A))`
          have hSub :
              interior (closure (interior A)) ⊆
                interior (closure (interior (A ∪ B ∪ C))) := by
            apply interior_mono
            apply closure_mono
            apply interior_mono
            intro y hy
            -- `y ∈ A` is certainly in `A ∪ B ∪ C`
            exact Or.inl (Or.inl hy)
          exact hSub hA
      | inr hB =>
          -- Handle the case `x ∈ interior (closure (interior B))`
          have hSub :
              interior (closure (interior B)) ⊆
                interior (closure (interior (A ∪ B ∪ C))) := by
            apply interior_mono
            apply closure_mono
            apply interior_mono
            intro y hy
            -- `y ∈ B` embeds into the union
            exact Or.inl (Or.inr hy)
          exact hSub hB
  | inr hC =>
      -- Handle the case `x ∈ interior (closure (interior C))`
      have hSub :
          interior (closure (interior C)) ⊆
            interior (closure (interior (A ∪ B ∪ C))) := by
        apply interior_mono
        apply closure_mono
        apply interior_mono
        intro y hy
        -- `y ∈ C` embeds into the union
        exact Or.inr hy
      exact hSub hC