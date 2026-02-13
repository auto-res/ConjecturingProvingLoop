

theorem Topology.interior_closure_eq_univ_iff_closure_eq_univ {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    · intro x _
      -- Since `interior (closure A) = univ`, every point belongs to it,
      -- hence to `closure A`.
      have : (x : X) ∈ interior (closure (A : Set X)) := by
        simpa [hInt]
      exact interior_subset this
  · intro hCl
    -- Rewrite using `hCl` and simplify with `interior_univ`.
    simpa [hCl, interior_univ]