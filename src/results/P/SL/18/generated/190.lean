

theorem interior_closure_eq_univ_iff_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (A : Set X)) = (Set.univ : Set X) ↔
      closure (A : Set X) = (Set.univ : Set X) := by
  classical
  constructor
  · intro hInt
    -- `interior (closure A)` is contained in `closure A`.
    have hSub : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
      interior_subset
    -- Using `hInt`, we obtain `univ ⊆ closure A`.
    have hLeft : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      simpa [hInt] using hSub
    -- Trivially, `closure A ⊆ univ`.
    have hRight : closure (A : Set X) ⊆ (Set.univ : Set X) := by
      intro _ _; trivial
    exact Set.Subset.antisymm hRight hLeft
  · intro hClos
    -- Rewrite the left‐hand side using `hClos` and simplify.
    simpa [hClos, interior_univ]