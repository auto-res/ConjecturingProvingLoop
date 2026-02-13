

theorem Topology.closureInterior_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) : closure (interior A) = closure A := by
  have hP1 : Topology.P1 (A := A) := Topology.P1_of_isOpen (A := A) hA
  simpa using (Topology.P1_iff_closureInterior_eq_closure (A := A)).1 hP1