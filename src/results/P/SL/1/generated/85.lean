

theorem Topology.interior_closure_eq_interior_closure_interior_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      interior (closure A) = interior (closure (interior A)) := by
  intro hP1
  -- From `P1` we know the closures are equal.
  have hcl : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Taking `interior` of both sides yields the desired equality.
  simpa using congrArg (fun S : Set X => interior S) hcl