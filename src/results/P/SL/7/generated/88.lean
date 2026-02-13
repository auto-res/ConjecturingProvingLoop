

theorem Topology.closureInterior_eq_closure_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : closure (interior A) = closure A := by
  have hP2 : Topology.P2 A := IsOpen_P2 (A := A) hA
  simpa using Topology.closureInterior_eq_closure_of_P2 (A := A) hP2