

theorem interior_closure_union_interior_eq {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure ((A : Set X) ∪ interior A)) = interior (closure (A : Set X)) := by
  have h := Topology.closure_union_interior_self (X := X) (A := A)
  simpa using congrArg interior h