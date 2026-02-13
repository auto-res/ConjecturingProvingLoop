

theorem Topology.P3_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P3 (A := A)) (hB : Topology.P3 (A := B)) (hC : Topology.P3 (A := C)) :
    Topology.P3 (A := A ∪ B ∪ C) := by
  have hAB : Topology.P3 (A := A ∪ B) :=
    Topology.P3_union (A := A) (B := B) hA hB
  simpa [Set.union_assoc] using
    (Topology.P3_union (A := A ∪ B) (B := C) hAB hC)