

theorem P1_of_closure_interior_closure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (closure (interior (closure A))) := by
  -- First, `interior (closure A)` satisfies `P1`.
  have hInt : Topology.P1 (interior (closure A)) := by
    simpa using Topology.P1_of_interior_closure (A := A)
  -- Taking the closure preserves `P1`.
  have hCl : Topology.P1 (closure (interior (closure A))) :=
    Topology.P1_closure_of_P1 (A := interior (closure A)) hInt
  simpa using hCl