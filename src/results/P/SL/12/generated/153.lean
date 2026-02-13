

theorem Topology.closure_interior_closure_eq_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    closure (interior (closure (A : Set X))) = closure (interior A) := by
  -- We show the two inclusions separately.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    -- From `P2` we already have the key inclusion on interiors.
    have h₁ :
        (interior (closure (A : Set X)) : Set X) ⊆ closure (interior A) :=
      Topology.interior_closure_subset_closure_interior_of_P2
        (X := X) (A := A) hA
    -- Taking closures preserves inclusion; simplify the right‐hand side.
    have h₂ :
        closure (interior (closure (A : Set X))) ⊆
          closure (closure (interior A)) :=
      closure_mono h₁
    simpa [closure_closure] using h₂
  · -- `⊇` direction
    -- `interior A` is contained in `interior (closure A)`.
    have h₁ :
        (interior (A : Set X)) ⊆ interior (closure A) :=
      Topology.interior_subset_interior_closure (X := X) (A := A)
    -- Taking closures yields the desired inclusion.
    have h₂ :
        closure (interior A) ⊆ closure (interior (closure A)) :=
      closure_mono h₁
    simpa using h₂