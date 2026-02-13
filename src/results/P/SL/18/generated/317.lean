

theorem P1_union_open_left {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hOpenA : IsOpen (A : Set X)) (hP1B : Topology.P1 B) :
    Topology.P1 (A ∪ B) := by
  have h := Topology.P1_union_open (A := B) (B := A) hP1B hOpenA
  simpa [Set.union_comm] using h