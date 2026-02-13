

theorem Topology.P2_inter_interiors {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∩ interior B) := by
  have hOpen : IsOpen ((interior A) ∩ (interior B) : Set X) :=
    isOpen_interior.inter isOpen_interior
  exact Topology.IsOpen_P2 (A := interior A ∩ interior B) hOpen