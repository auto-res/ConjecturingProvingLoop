

theorem isOpen_union_P2 {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    Topology.P2 (A ∪ B) := by
  -- The union of two open sets is open
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  -- Apply the existing result for open sets
  exact Topology.isOpen_P2 (A := A ∪ B) hOpen