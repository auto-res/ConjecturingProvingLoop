

theorem Topology.interior_closure_iInter_subset_iInter_interior_closure
    {X : Type*} [TopologicalSpace X] {ι : Type*} {s : ι → Set X} :
    interior (closure (⋂ i, s i : Set X)) ⊆ ⋂ i, interior (closure (s i)) := by
  intro x hx
  -- For each index `i`, we show that `x` belongs to `interior (closure (s i))`.
  have h : ∀ i, x ∈ interior (closure (s i)) := by
    intro i
    -- Since `⋂ j, s j ⊆ s i`, the same holds after taking closures and interiors.
    have hSub : (⋂ j, s j : Set X) ⊆ s i := by
      intro y hy
      exact (Set.mem_iInter.1 hy) i
    have hCl : closure (⋂ j, s j : Set X) ⊆ closure (s i) :=
      closure_mono hSub
    have hInt :
        interior (closure (⋂ j, s j : Set X)) ⊆ interior (closure (s i)) :=
      interior_mono hCl
    exact hInt hx
  -- Combine the pointwise facts into membership in the intersection.
  exact Set.mem_iInter.2 h