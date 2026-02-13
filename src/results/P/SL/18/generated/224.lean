

theorem P3_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P3 (closure (A : Set X)) := by
  intro hDenseInt
  -- From the density of `interior A`, deduce the density of `A`.
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  -- Apply the existing result that dense sets yield `P3` for their closures.
  exact Topology.P3_closure_of_dense (A := A) hDenseA