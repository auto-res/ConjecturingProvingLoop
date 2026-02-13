

theorem P3_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X)) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hPA hPB
  -- Convert `P3` for `A` and `B` into openness, using the closed–open equivalence.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) := hOpenA.inter hOpenB
  -- Every open set satisfies `P3`.
  exact (Topology.isOpen_has_all_Ps (X := X) (A := (A ∩ B : Set X)) hOpenInter).2.2