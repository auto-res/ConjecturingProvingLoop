

theorem P3_closed_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B) :
    Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  -- From the closedness and `P3` property we deduce that `A` and `B` are open
  have hOpenA : IsOpen A :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := A) hA_closed).1 hP3A
  have hOpenB : IsOpen B :=
    (Topology.P3_closed_iff_isOpen (X := X) (A := B) hB_closed).1 hP3B
  -- The intersection of open (resp. closed) sets is open (resp. closed)
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  have hClosedInter : IsClosed (A ∩ B) := hA_closed.inter hB_closed
  -- Apply the closed–open equivalence for `P3` to the intersection
  exact
    (Topology.P3_closed_iff_isOpen (X := X) (A := A ∩ B) hClosedInter).2
      hOpenInter