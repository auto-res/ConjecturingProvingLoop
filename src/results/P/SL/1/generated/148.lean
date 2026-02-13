

theorem Topology.interior_closure_interior_closure_eq_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure A))) = interior (closure A) := by
  -- First inclusion: `⊆`
  apply Set.Subset.antisymm
  ·
    have h :=
      interior_closure_interior_subset_interior_closure (A := closure A)
    simpa [closure_closure] using h
  ·
    -- Second inclusion: `⊇`
    intro x hx
    -- `interior (closure A)` is open.
    have hOpen : IsOpen (interior (closure A)) := isOpen_interior
    -- It is contained in its own closure.
    have hsubset : (interior (closure A) : Set X) ⊆
        closure (interior (closure A)) := by
      intro y hy
      exact subset_closure hy
    -- Hence it is contained in the interior of that closure.
    have h' : (interior (closure A) : Set X) ⊆
        interior (closure (interior (closure A))) :=
      interior_maximal hsubset hOpen
    exact h' hx