

theorem interior_closure_eq_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P1 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  -- From `P1`, we know the closures coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hA
  -- Taking `interior` of both sides yields the desired equality.
  simpa using congrArg interior hEq