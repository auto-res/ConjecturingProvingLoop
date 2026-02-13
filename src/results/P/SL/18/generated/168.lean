

theorem closure_interior_iInter_subset
    {ι : Sort _} {X : Type _} [TopologicalSpace X] (A : ι → Set X) :
    closure (interior (⋂ i, A i : Set X)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- Show that `x ∈ closure (interior (A i))` for every index `i`.
  have hx_i : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- `interior` is monotone with respect to set inclusion.
    have hSub_int : interior (⋂ j, A j : Set X) ⊆ interior (A i) := by
      apply interior_mono
      -- The intersection is contained in each component.
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    -- Taking closures preserves inclusions.
    have hSub_clos :
        closure (interior (⋂ j, A j : Set X)) ⊆
          closure (interior (A i)) :=
      closure_mono hSub_int
    exact hSub_clos hx
  -- Assemble the pointwise membership into the intersection.
  exact Set.mem_iInter.2 hx_i