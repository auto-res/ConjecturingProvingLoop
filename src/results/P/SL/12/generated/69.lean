

theorem Topology.interior_closure_interior_closure_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (interior (A : Set X))))) =
      interior (closure (interior A)) := by
  -- We establish the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- Step 1: `interior (closure (interior A)) ⊆ closure (interior A)`.
    have h₁ :
        (interior (closure (interior A)) : Set X) ⊆ closure (interior A) :=
      interior_subset
    -- Step 2: take closures of both sides.
    have h₂ :
        closure (interior (closure (interior A))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    -- Step 3: simplify the right‐hand side.
    have h₂' :
        closure (interior (closure (interior A))) ⊆
          closure (interior A) := by
      simpa [closure_closure] using h₂
    -- Step 4: take interiors once more.
    exact interior_mono h₂'
  · -- `⊇` direction
    -- The set `interior (closure (interior A))` is open.
    have h_open : IsOpen (interior (closure (interior A))) := isOpen_interior
    -- It is contained in its own closure, hence in the larger closure that appears.
    have h_subset :
        (interior (closure (interior A)) : Set X) ⊆
          closure (interior (closure (interior (A : Set X)))) := by
      simpa using
        (subset_closure :
          (interior (closure (interior A)) : Set X) ⊆
            closure (interior (closure (interior A))))
    -- Apply maximality of the interior for an open set.
    have h_incl :
        interior (closure (interior A)) ⊆
          interior (closure (interior (closure (interior A)))) :=
      interior_maximal h_subset h_open
    -- Conclude the desired inclusion.
    simpa using h_incl