

theorem P2_union_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP2A : Topology.P2 A) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  -- Translate `P2` for the closed sets `A` and `B` into openness.
  have hOpenA : IsOpen A :=
    (Topology.P2_closed_iff_open (A := A) hA_closed).1 hP2A
  have hOpenB : IsOpen B :=
    (Topology.P2_closed_iff_open (A := B) hB_closed).1 hP2B
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B) := hOpenA.union hOpenB
  -- Apply `P2` for open sets.
  exact Topology.P2_of_open hOpenUnion