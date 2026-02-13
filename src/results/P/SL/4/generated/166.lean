

theorem interior_closure_eq_univ_iff {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) = (Set.univ : Set X) ↔ closure A = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- Show the two sets are equal by extensionality.
    ext x
    constructor
    · intro _hx
      -- Any point in `closure A` is trivially in `univ`.
      trivial
    · intro _hx
      -- Since `interior (closure A) = univ`, every point of `univ` lies in
      -- `interior (closure A)`, and hence in `closure A`.
      have : x ∈ interior (closure A) := by
        simpa [hInt] using (by
          -- `x` is an arbitrary point of `univ`.
          trivial : x ∈ (Set.univ : Set X))
      exact interior_subset this
  · intro hCl
    -- Rewrite the left‐hand side using `hCl` and simplify.
    simpa [hCl, interior_univ]