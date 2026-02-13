

theorem open_closure_interior_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (A : Set X) → IsOpen (closure A) → IsOpen (closure (interior A)) := by
  intro hP2 hOpen
  have hEq : closure (interior (A : Set X)) = closure A :=
    Topology.P2_implies_closure_interior_eq_closure (A := A) hP2
  simpa [hEq] using hOpen