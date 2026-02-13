

theorem Topology.closure_interior_closure_idempotent {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure (interior (closure (interior (closure (A : Set X))))) =
      closure (interior (closure (A : Set X))) := by
  -- We establish the two inclusions separately and conclude by antisymmetry.
  apply Set.Subset.antisymm
  · -- `⊆` direction
    have h1 :
        interior (closure (interior (closure (A : Set X)))) ⊆
          closure (interior (closure (A : Set X))) := by
      -- An interior is always contained in the set it is taken from.
      simpa using
        (interior_subset :
          interior (closure (interior (closure (A : Set X)))) ⊆
            closure (interior (closure (A : Set X))))
    -- Taking closures preserves inclusion; `closure (closure _)` simplifies.
    simpa [closure_closure] using closure_mono h1
  · -- `⊇` direction
    have h2 :
        closure (interior (closure (A : Set X))) ⊆
          closure (interior (closure (interior (closure (A : Set X))))) := by
      -- Use the generic monotonicity lemma with `A := interior (closure A)`.
      have h :
          closure (interior (interior (closure (A : Set X)))) ⊆
            closure (interior (closure (interior (closure (A : Set X))))) :=
        Topology.closure_interior_subset_closure_interior_closure
          (X := X) (A := interior (closure (A : Set X)))
      simpa [interior_interior] using h
    exact h2