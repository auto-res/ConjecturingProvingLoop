

theorem P123_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) ∧
      Topology.P2 (interior A ∪ interior B) ∧
      Topology.P3 (interior A ∪ interior B) := by
  -- `interior A` and `interior B` are open sets.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- Apply the existing lemma for the union of two open sets.
  simpa using
    (Topology.P123_union_open
      (A := interior A) (B := interior B) hOpenA hOpenB)