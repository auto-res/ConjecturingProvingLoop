

theorem Topology.interiorClosureInterior_eq_univ_iff_closureInterior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) = (Set.univ : Set X) ↔
      closure (interior A) = (Set.univ : Set X) := by
  constructor
  · intro h
    -- `interior (closure (interior A))` is contained in `closure (interior A)`.
    have hSub : interior (closure (interior A)) ⊆ closure (interior A) :=
      interior_subset
    -- Hence `univ ⊆ closure (interior A)`.
    have hIncl : (Set.univ : Set X) ⊆ closure (interior A) := by
      simpa [h] using hSub
    -- The reverse inclusion is immediate.
    exact Set.Subset.antisymm (Set.Subset_univ _) hIncl
  · intro h
    simpa [h, interior_univ]