

theorem Topology.P2_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  -- First, `closure A` is the whole space because `interior A` is dense.
  have hclosure : closure A = (Set.univ : Set X) :=
    Topology.closure_eq_univ_of_dense_interior (A := A) hDense
  -- Unfold the definition of `P2` and prove the subset relation.
  dsimp [Topology.P2]
  intro x hx
  -- After rewriting everything in terms of `univ`, the goal becomes tautological.
  simpa [hclosure, interior_univ, closure_univ] using
    (by
      have : x ∈ (Set.univ : Set X) := by
        simp
      simpa using this)