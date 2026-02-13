

theorem closure_interior_iInter_subset {X ι : Type*} [TopologicalSpace X] {A : ι → Set X} :
    closure (interior (⋂ i, A i)) ⊆ ⋂ i, closure (interior (A i)) := by
  intro x hx
  -- For every `i`, show `x ∈ closure (interior (A i))`.
  have hxAll : ∀ i, x ∈ closure (interior (A i)) := by
    intro i
    -- Use monotonicity of `interior` and `closure` together with the basic set inclusion.
    have hsubset : closure (interior (⋂ j, A j)) ⊆ closure (interior (A i)) := by
      apply closure_mono
      apply interior_mono
      exact Set.iInter_subset (fun j => A j) i
    exact hsubset hx
  -- Assemble the witnesses into the intersection.
  exact Set.mem_iInter.2 hxAll