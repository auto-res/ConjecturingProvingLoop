

theorem Topology.P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 (A := A)) (hB : Topology.P2 (A := B)) (hC : Topology.P2 (A := C)) :
    Topology.P2 (A := A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P2 (A := A ∪ B) :=
    Topology.P2_union (A := A) (B := B) hA hB
  -- Now union the result with `C`.
  simpa [Set.union_assoc] using
    (Topology.P2_union (A := A ∪ B) (B := C) hAB hC)