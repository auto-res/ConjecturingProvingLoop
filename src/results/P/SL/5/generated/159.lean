

theorem interior_closure_eq_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P3 (X := X) A) :
    interior (closure (A : Set X)) =
      interior (closure (interior (closure A))) := by
  -- `P3` gives an equality between the two closures.
  have h :=
    Topology.closure_eq_closure_interior_closure_of_P3
      (X := X) (A := A) hA
  -- Taking `interior` of both sides yields the desired result.
  simpa using congrArg interior h