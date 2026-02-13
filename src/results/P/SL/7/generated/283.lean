

theorem Topology.isOpen_closureInterior_iff_isOpen_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    IsOpen (closure (interior A)) ↔ IsOpen (closure (A : Set X)) := by
  -- From `P1` we have `closure A = closure (interior A)`.
  have hEq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (A := A)).1 hP1
  constructor
  · intro hOpen
    simpa [hEq] using hOpen
  · intro hOpen
    simpa [hEq] using hOpen