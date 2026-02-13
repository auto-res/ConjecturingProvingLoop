

theorem P2_closure_of_dense_interior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hDenseInt
  -- `Dense (interior A)` implies `Dense A`.
  have hDenseA : Dense (A : Set X) :=
    Topology.dense_of_dense_interior (A := A) hDenseInt
  -- Apply the existing lemma for dense sets.
  exact Topology.P2_closure_of_dense (A := A) hDenseA