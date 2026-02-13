

theorem Topology.P1_union_three
    {X : Type*} [TopologicalSpace X] {A B C : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) :
    Topology.P1 (A ∪ B ∪ C) := by
  -- First, obtain `P1` for `A ∪ B`.
  have hAB : Topology.P1 (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Next, union the result with `C`.
  have hABC : Topology.P1 ((A ∪ B) ∪ C) :=
    Topology.P1_union (X := X) (A := A ∪ B) (B := C) hAB hC
  -- Rewrite to the desired (left-associative) form.
  simpa [Set.union_assoc] using hABC