

theorem Topology.P2_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) :
    Topology.P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC