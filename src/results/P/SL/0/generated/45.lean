

theorem P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P2 A → Topology.P2 B → Topology.P2 (A ∩ B) := by
  intro hPA hPB
  -- Translate `P2` for the closed sets `A` and `B` into openness.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Every open set satisfies `P2`.
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpenInter).2.1