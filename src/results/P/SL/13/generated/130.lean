

theorem Topology.closed_dense_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) A := by
  -- A closed and dense set is the whole space.
  have h_eq : (A : Set X) = (Set.univ : Set X) :=
    Topology.closed_dense_eq_univ (X := X) (A := A) hA_closed hA_dense
  -- `P1` holds for the whole space; rewrite via `h_eq`.
  simpa [h_eq] using Topology.P1_univ (X := X)