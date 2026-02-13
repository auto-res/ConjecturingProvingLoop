

theorem interior_closure_eq_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : Topology.P2 (X := X) A) :
    interior (closure (A : Set X)) = interior (closure (interior A)) := by
  have h := Topology.closure_eq_closure_interior_of_P2 (X := X) (A := A) hA
  simpa using congrArg interior h