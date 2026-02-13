

theorem Topology.P1_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 (A := A)) (hB : Topology.P1 (A := B))
    (hC : Topology.P1 (A := C)) :
    Topology.P1 (A := A ∪ B ∪ C) := by
  -- First, combine `A` and `B`.
  have hAB : Topology.P1 (A := A ∪ B) :=
    Topology.P1_union (A := A) (B := B) hA hB
  -- Now union the result with `C`.
  simpa [Set.union_assoc] using
    (Topology.P1_union (A := A ∪ B) (B := C) hAB hC)