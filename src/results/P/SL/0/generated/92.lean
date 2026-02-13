

theorem P2_inter_three_of_closed {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) (hC : IsClosed (C : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∩ B ∩ C) := by
  intro hPA hPB hPC
  -- Translate each `P2` on a closed set into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := C) hC).1 hPC
  -- The triple intersection of open sets is open.
  have hOpenInter : IsOpen ((A ∩ B ∩ C) : Set X) := (hOpenA.inter hOpenB).inter hOpenC
  -- Every open set satisfies `P2`.
  exact
    (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B ∩ C : Set X)) hOpenInter).2.1