

theorem Topology.isOpen_closureInterior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hOpen : IsOpen (closure (A : Set X))) :
    IsOpen (closure (interior A)) := by
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  simpa [hEq] using hOpen