

theorem Topology.interior_closure_eq_interior_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = interior (closure (interior (closure A))) := by
  apply Set.Subset.antisymm
  ·
    -- `interior (closure A)` is open and contained in `closure (interior (closure A))`.
    have hsubset : interior (closure A) ⊆ closure (interior (closure A)) := by
      intro x hx
      exact subset_closure hx
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- Hence it is contained in the interior of that closure.
    exact interior_maximal hsubset hOpen
  ·
    -- Use the previously established inclusion for the reverse direction.
    have hsubset :
        interior (closure (interior (closure A))) ⊆
          interior (closure (closure A)) :=
      interior_closure_interior_subset_interior_closure (A := closure A)
    -- Simplify with the equality `interior (closure (closure A)) = interior (closure A)`.
    simpa [Topology.interior_closure_closure_eq_interior_closure (A := A)] using hsubset