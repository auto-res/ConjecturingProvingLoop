

theorem Topology.closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The union of two open sets is open.
  have hUnionOpen : IsOpen (A ∪ B) := hA.union hB
  -- For an open set, its interior is itself.
  have hIntEq : interior (A ∪ B) = A ∪ B := hUnionOpen.interior_eq
  -- Rewrite and use the standard formula for the closure of a union.
  simpa [hIntEq, closure_union]