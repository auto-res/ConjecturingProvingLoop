

theorem Topology.P2_closure_of_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hDense : Dense A) : Topology.P2 (closure A) := by
  -- Obtain `P3` for `closure A` from the density of `A`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.P3_closure_of_dense (A := A) hDense
  -- Use the equivalence `P2 (closure A) ↔ P3 (closure A)` to get `P2`.
  exact (Topology.P2_closure_iff_P3_closure (A := A)).2 hP3