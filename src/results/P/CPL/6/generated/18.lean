

theorem P2_union3 {X : Type*} [TopologicalSpace X] {A B C : Set X} : Topology.P2 A → Topology.P2 B → Topology.P2 C → Topology.P2 (A ∪ B ∪ C) := by
  intro hP2A hP2B hP2C
  -- First, get `P2` for `A ∪ B`.
  have hP2AB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (A := A) (B := B) hP2A hP2B
  -- Then, combine with `C`.
  have hP2ABC : Topology.P2 ((A ∪ B) ∪ C) :=
    Topology.P2_union (A := A ∪ B) (B := C) hP2AB hP2C
  -- Rearrange the unions to match the desired shape.
  simpa [Set.union_assoc] using hP2ABC