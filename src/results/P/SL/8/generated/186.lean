

theorem closed_P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∩ B) := by
  -- `A` and `B` are closed and satisfy `P2`, hence they are open.
  have hOpenA : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hA_closed hP2A
  have hOpenB : IsOpen B :=
    Topology.closed_P2_isOpen (X := X) (A := B) hB_closed hP2B
  -- The intersection of two open sets is open, and open sets satisfy `P2`.
  simpa using
    isOpen_inter_imp_P2 (X := X) (A := A) (B := B) hOpenA hOpenB