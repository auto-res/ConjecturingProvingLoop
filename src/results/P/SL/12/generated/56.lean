

theorem Topology.interior_closure_interior_closure_eq
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (closure (A : Set X)))) =
      interior (closure A) := by
  -- We show the two inclusions separately.
  apply Set.Subset.antisymm
  · -- First inclusion: `⊆`
    have h_cl :
        closure (interior (closure (A : Set X))) ⊆ closure A := by
      -- `interior (closure A) ⊆ closure A`
      have h₁ : (interior (closure (A : Set X)) : Set X) ⊆ closure A :=
        interior_subset
      -- Taking closures preserves this inclusion.
      have h₂ :
          closure (interior (closure (A : Set X))) ⊆
            closure (closure (A : Set X)) :=
        closure_mono h₁
      simpa [closure_closure] using h₂
    -- Monotonicity of `interior` yields the desired inclusion.
    exact interior_mono h_cl
  · -- Second inclusion: `⊇`
    -- `interior (closure A)` is open.
    have h_open : IsOpen (interior (closure (A : Set X))) := isOpen_interior
    -- It is contained in `closure (interior (closure A))`.
    have h_sub :
        (interior (closure (A : Set X)) : Set X) ⊆
          closure (interior (closure (A : Set X))) :=
      subset_closure
    -- An open set contained in a set lies in its interior.
    have h_incl :
        interior (closure (A : Set X)) ⊆
          interior (closure (interior (closure (A : Set X)))) :=
      interior_maximal h_sub h_open
    exact h_incl