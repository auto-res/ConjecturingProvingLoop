

theorem Topology.P2_closureInterior_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X)))) :
    Topology.P2 (closure (interior (A : Set X))) := by
  have hEquiv := (Topology.P2_closureInterior_iff_isOpen (A := A))
  exact (hEquiv).2 hOpen