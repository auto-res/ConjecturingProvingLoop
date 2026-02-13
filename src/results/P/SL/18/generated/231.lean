

theorem interior_closure_interior_eq_empty_iff
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (∅ : Set X) ↔
      interior (A : Set X) = ∅ := by
  classical
  constructor
  · intro h
    -- `interior A` is contained in `interior (closure (interior A))`,
    -- hence it must also be empty.
    have hSub :
        interior (A : Set X) ⊆ (∅ : Set X) := by
      intro x hx
      have : x ∈ interior (closure (interior (A : Set X))) :=
        Topology.interior_subset_interior_closure_interior (A := A) hx
      simpa [h] using this
    exact Set.Subset.antisymm hSub (Set.empty_subset _)
  · intro hInt
    -- If `interior A` is empty, so is its closure, and consequently
    -- the interior of that closure is also empty.
    have hClos : closure (interior (A : Set X)) = (∅ : Set X) := by
      simpa [hInt, closure_empty]
    simpa [hClos, interior_empty]