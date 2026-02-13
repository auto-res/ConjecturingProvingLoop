

theorem isOpen_closure_of_P1_and_open_closure_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpen : IsOpen (closure (interior A))) :
    IsOpen (closure A) := by
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  simpa [hEq] using hOpen