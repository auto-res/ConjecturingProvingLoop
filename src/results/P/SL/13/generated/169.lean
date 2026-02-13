

theorem Topology.dense_iff_interior_closure_eq_univ {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact Topology.dense_implies_interior_closure_eq_univ (X := X) (A := A) hDense
  · intro hInt
    -- From the assumption we first show `closure A = univ`.
    have hClosure : closure (A : Set X) = (Set.univ : Set X) := by
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · -- Since `interior (closure A)` equals `univ`, and `interior (closure A) ⊆ closure A`,
        -- the inclusion `univ ⊆ closure A` follows.
        have : interior (closure (A : Set X)) ⊆ closure (A : Set X) :=
          interior_subset
        simpa [hInt] using this
    -- Rewriting `Dense` shows the desired result.
    simpa [Dense, hClosure] using hClosure