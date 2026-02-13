

theorem interior_closure_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    interior (closure (⋂ i, A i : Set X)) ⊆ ⋂ i, interior (closure (A i)) := by
  intro x hx
  -- Show that `x` belongs to `interior (closure (A i))` for every `i`.
  have hx_i : ∀ i, x ∈ interior (closure (A i)) := by
    intro i
    -- `closure` is monotone with respect to set inclusion.
    have h_closure_subset :
        closure (⋂ j, A j : Set X) ⊆ closure (A i) := by
      apply closure_mono
      intro y hy
      -- Membership in the intersection yields membership in each component.
      exact (Set.mem_iInter.1 hy) i
    -- Taking interiors preserves inclusions.
    have h_interior_subset :
        interior (closure (⋂ j, A j : Set X)) ⊆
          interior (closure (A i)) :=
      interior_mono h_closure_subset
    exact h_interior_subset hx
  -- Assemble the pointwise condition into membership in the intersection.
  exact Set.mem_iInter.2 hx_i