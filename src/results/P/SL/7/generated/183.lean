

theorem Topology.isOpen_closureInterior_iff_isOpen_closure_of_P2
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) :
    IsOpen (closure (interior A)) ↔ IsOpen (closure (A : Set X)) := by
  -- From `P2` we know the closures coincide.
  have hEq : closure (interior A) = closure (A : Set X) :=
    Topology.closureInterior_eq_closure_of_P2 (A := A) hP2
  -- Rewriting one side of the equivalence with this equality
  -- turns both sides into the same statement, giving a trivial equivalence.
  simpa [hEq] using
    (Iff.rfl :
      IsOpen (closure (interior A)) ↔ IsOpen (closure (interior A)))