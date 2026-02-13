

theorem Topology.closure_interior_union_eq_closure_union_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
  have hUnion : IsOpen (A ∪ B) := hA.union hB
  simpa using
    (Topology.closure_interior_eq_closure_of_isOpen (A := A ∪ B) hUnion)