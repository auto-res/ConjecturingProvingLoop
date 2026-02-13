

theorem Topology.interior_closure_interior_idempotent
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure A) := by
  -- We prove the two inclusions separately and conclude by extensionality.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- First, note `interior (closure A) ⊆ closure A`.
    have h₁ :
        (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
      interior_subset
    -- Taking closures preserves inclusions.
    have h₂ :
        closure (interior (closure (A : Set X))) ⊆
          closure (closure (A : Set X)) :=
      closure_mono h₁
    -- Simplify `closure (closure A)` and apply monotonicity of `interior`.
    have h₃ :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      simpa [closure_closure] using h₂
    -- Finally, `interior` is monotone.
    exact interior_mono h₃
  · -- `⊇` direction
    -- The set `interior (closure A)` is open …
    have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- … and contained in `closure (interior (closure A))`.
    have h_subset :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    -- By maximality of the interior of an open set, it is contained in the
    -- interior of any superset—here `closure (interior (closure A))`.
    have h_interior :
        interior (closure (A : Set X)) ⊆
          interior (closure (interior (closure A))) :=
      interior_maximal h_subset h_open
    -- This is exactly the desired inclusion.
    simpa using h_interior