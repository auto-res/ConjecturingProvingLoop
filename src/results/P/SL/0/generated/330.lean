

theorem P3_inter_four_of_closed {X : Type*} [TopologicalSpace X]
    {A B C D : Set X}
    (hA : IsClosed (A : Set X)) (hB : IsClosed (B : Set X))
    (hC : IsClosed (C : Set X)) (hD : IsClosed (D : Set X)) :
    Topology.P3 A → Topology.P3 B → Topology.P3 C → Topology.P3 D →
      Topology.P3 (A ∩ B ∩ C ∩ D) := by
  intro hPA hPB hPC hPD
  -- From `P3` on closed sets, obtain that each set is open.
  have hOpenA : IsOpen (A : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := A) hA).1 hPA
  have hOpenB : IsOpen (B : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := B) hB).1 hPB
  have hOpenC : IsOpen (C : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := C) hC).1 hPC
  have hOpenD : IsOpen (D : Set X) :=
    (Topology.P3_iff_isOpen_of_isClosed (X := X) (A := D) hD).1 hPD
  -- The intersection of four open sets is open.
  have hOpenInter : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hOpenA.inter hOpenB).inter hOpenC).inter hOpenD)
  -- Every open set satisfies `P3`.
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := (A ∩ B ∩ C ∩ D : Set X))
        hOpenInter).2.2