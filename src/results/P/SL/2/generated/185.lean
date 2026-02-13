

theorem Topology.P2_closure_implies_isOpen_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P2 (closure (A : Set X)) → IsOpen (closure (A : Set X)) := by
  intro hP2Cl
  exact (Topology.P2_closure_iff_isOpen_closure (A := A)).1 hP2Cl