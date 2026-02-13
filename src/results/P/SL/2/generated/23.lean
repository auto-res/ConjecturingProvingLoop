

theorem Topology.isOpen_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    IsOpen A → closure (interior A) = closure A := by
  intro hA
  have hP2 : Topology.P2 A := Topology.isOpen_implies_P2 (A := A) hA
  exact Topology.P2_implies_closure_interior_eq_closure (A := A) hP2