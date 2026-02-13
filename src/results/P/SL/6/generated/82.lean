

theorem interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (interior (closure (A : Set X)))) = interior (closure A) := by
  -- We prove the equality by showing mutual inclusion.
  apply Set.Subset.antisymm
  · -- First, `⊆`.
    have h :
        interior (closure (interior (closure (A : Set X))))
          ⊆ interior (closure (closure (A : Set X))) :=
      interior_closure_interior_subset_closure (A := closure (A : Set X))
    simpa [closure_closure] using h
  · -- Second, `⊇`.
    -- `interior (closure A)` is open and contained in `closure (interior (closure A))`.
    have hSub :
        interior (closure (A : Set X))
          ⊆ closure (interior (closure (A : Set X))) :=
      subset_closure
    have hIncl :
        interior (closure (A : Set X))
          ⊆ interior (closure (interior (closure A))) :=
      interior_maximal hSub isOpen_interior
    simpa using hIncl