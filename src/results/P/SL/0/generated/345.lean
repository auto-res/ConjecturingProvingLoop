

theorem P2_inter_four_of_closed {X : Type*} [TopologicalSpace X] {A B C D : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hC_closed : IsClosed (C : Set X)) (hD_closed : IsClosed (D : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 D →
      Topology.P2 (A ∩ B ∩ C ∩ D) := by
  intro hPA hPB hPC hPD
  -- Convert each `P2` on a closed set into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := A) hA_closed) hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := B) hB_closed) hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := C) hC_closed) hPC
  have hOpenD : IsOpen (D : Set X) :=
    (Topology.isOpen_of_isClosed_and_P2 (X := X) (A := D) hD_closed) hPD
  -- The intersection of four open sets is open, hence satisfies `P2`.
  exact
    (Topology.P2_inter_four_of_open (X := X) (A := A) (B := B) (C := C) (D := D)
        hOpenA hOpenB hOpenC hOpenD)