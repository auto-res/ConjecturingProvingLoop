

theorem P2_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP2B : Topology.P2 B) :
    Topology.P2 (A ∪ B) := by
  have h : Topology.P2 (B ∪ A) :=
    Topology.P2_union_open (A := B) (B := A) hP2B hOpenA
  simpa [Set.union_comm] using h