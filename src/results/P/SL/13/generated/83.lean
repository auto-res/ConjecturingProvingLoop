

theorem Topology.dense_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P1 (X := X) (closure (A : Set X)) := by
  -- The closure of a dense set is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- P1 holds for the whole space.
  have hP1_univ : Topology.P1 (X := X) (Set.univ : Set X) :=
    Topology.P1_univ (X := X)
  -- Rewrite via `h_closure`.
  simpa [h_closure] using hP1_univ