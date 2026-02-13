

theorem interior_closure_interior_eq_univ_iff_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior (A : Set X))) = (Set.univ : Set X) ↔
      closure (interior (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hInt
    -- `interior s ⊆ s`, so the given equality forces
    -- `closure (interior A)` to cover the whole space.
    have hSub : (Set.univ : Set X) ⊆ closure (interior (A : Set X)) := by
      have hIncl :
          interior (closure (interior (A : Set X))) ⊆
            closure (interior (A : Set X)) :=
        interior_subset
      simpa [hInt] using hIncl
    -- The reverse inclusion is trivial.
    have hSup : closure (interior (A : Set X)) ⊆ (Set.univ : Set X) :=
      Set.subset_univ _
    exact Set.Subset.antisymm hSup hSub
  · intro hClos
    -- Rewriting with the hypothesis and `interior_univ`.
    have hEq :
        interior (closure (interior (A : Set X))) =
          interior (Set.univ : Set X) := by
      simpa [hClos]
    simpa [interior_univ] using hEq