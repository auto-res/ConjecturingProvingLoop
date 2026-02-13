

theorem Topology.dense_implies_P3_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_dense : Dense (A : Set X)) :
    Topology.P3 (X := X) (closure (A : Set X)) := by
  -- The closure of a dense set is the whole space.
  have h_closure : closure (A : Set X) = (Set.univ : Set X) := hA_dense.closure_eq
  -- `P3` holds for the whole space.
  have hP3_univ : Topology.P3 (X := X) (Set.univ : Set X) :=
    Topology.P3_univ (X := X)
  -- Rewrite using `h_closure`.
  simpa [h_closure] using hP3_univ