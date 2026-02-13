

theorem Topology.P1_interior_inter {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∩ interior B) := by
  -- Both `interior A` and `interior B` are open.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- The intersection of two open sets is open, hence satisfies `P1`.
  exact Topology.P1_inter_of_isOpen
    (A := interior A) (B := interior B) hOpenA hOpenB