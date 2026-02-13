

theorem Topology.closed_P3_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hP3A : Topology.P3 (X := X) A) (hP3B : Topology.P3 (X := X) B) :
    Topology.P3 (X := X) (A ∩ B) := by
  -- From `hAclosed` and `hP3A`, `A` is open.
  have hOpenA : IsOpen A :=
    Topology.closed_P3_isOpen (X := X) (A := A) hAclosed hP3A
  -- From `hBclosed` and `hP3B`, `B` is open.
  have hOpenB : IsOpen B :=
    Topology.closed_P3_isOpen (X := X) (A := B) hBclosed hP3B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Any open set satisfies `P3`.
  exact Topology.isOpen_implies_P3 (X := X) (A := A ∩ B) hOpenInter