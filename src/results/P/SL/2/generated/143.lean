

theorem Topology.dense_iff_interior_closure_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (A : Set X) ↔ interior (closure (A : Set X)) = (Set.univ : Set X) := by
  constructor
  · intro hDense
    exact
      (Topology.dense_implies_interior_closure_eq_univ (A := A)) hDense
  · intro hIntEq
    -- First, show `closure A = univ`.
    have hSub : (Set.univ : Set X) ⊆ closure (A : Set X) := by
      intro x hx
      have hxInt : x ∈ interior (closure (A : Set X)) := by
        simpa [hIntEq] using hx
      exact interior_subset hxInt
    have hClosureEq : closure (A : Set X) = (Set.univ : Set X) := by
      apply subset_antisymm
      · intro x hx; simp
      · exact hSub
    -- Conclude density from the closure equality.
    simpa [Dense, hClosureEq] using hClosureEq