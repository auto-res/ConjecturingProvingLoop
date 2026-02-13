

theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : closure (A : Set X) = Set.univ) :
    Topology.P3 A := by
  -- From the closure equality, deduce density of `A`.
  have hDense : Dense (A : Set X) :=
    (Topology.dense_iff_closure_eq_univ (A := A)).2 h
  -- Density implies `P3`.
  exact Topology.P3_of_dense (X := X) hDense