

theorem Topology.closure_has_P2_of_denseInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior A) → Topology.P2 (closure A) := by
  intro hDense
  -- From the density of `interior A`, we know `closure A` satisfies `P3`.
  have hP3 : Topology.P3 (closure A) :=
    Topology.closure_has_P3_of_denseInterior (X := X) (A := A) hDense
  -- A `P3` closure yields `P2` for the same closure.
  exact Topology.P2_of_P3_closure (X := X) (A := A) hP3