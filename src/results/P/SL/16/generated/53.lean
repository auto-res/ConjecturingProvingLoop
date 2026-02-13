

theorem Topology.closed_P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hP2A : Topology.P2 (X := X) A) (hP2B : Topology.P2 (X := X) B) :
    Topology.P2 (X := X) (A ∩ B) := by
  -- From `hAclosed` and `hP2A`, `A` is open.
  have hOpenA : IsOpen A :=
    Topology.closed_P2_isOpen (X := X) (A := A) hAclosed hP2A
  -- From `hBclosed` and `hP2B`, `B` is open.
  have hOpenB : IsOpen B :=
    Topology.closed_P2_isOpen (X := X) (A := B) hBclosed hP2B
  -- The intersection of two open sets is open.
  have hOpenInter : IsOpen (A ∩ B) := hOpenA.inter hOpenB
  -- Any open set satisfies `P2`.
  exact Topology.isOpen_implies_P2 (X := X) (A := A ∩ B) hOpenInter