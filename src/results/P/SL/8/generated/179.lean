

theorem closed_P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    Topology.P3 (A ∩ B) := by
  -- Both `A` and `B` are closed and satisfy `P3`, hence they are open.
  have hOpenA : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hA_closed hP3A
  have hOpenB : IsOpen B :=
    Topology.closed_P3_isOpen (X := X) (A := B) hB_closed hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := IsOpen.inter hOpenA hOpenB
  -- Openness implies `P3`.
  simpa using
    Topology.isOpen_imp_P3 (X := X) (A := A ∩ B) hOpenInter