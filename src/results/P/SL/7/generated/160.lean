

theorem Topology.P2_of_open_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsOpen (closure (A : Set X)) → Topology.P2 (closure (A : Set X)) := by
  intro hOpen
  have hEquiv := (Topology.P2_closure_iff_isOpen (A := A))
  exact (hEquiv).2 hOpen