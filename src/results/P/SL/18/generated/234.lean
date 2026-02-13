

theorem P123_of_dense_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed (A : Set X)) (hDense : Dense (A : Set X)) :
    Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  -- A closed dense subset of a topological space is the whole space.
  have hEq : (A : Set X) = Set.univ :=
    Topology.dense_closed_eq_univ (A := A) hDense hClosed
  -- All three properties `P1`, `P2`, and `P3` hold for `univ`; rewrite using `hEq`.
  simpa [hEq] using (Topology.P123_univ (X := X))