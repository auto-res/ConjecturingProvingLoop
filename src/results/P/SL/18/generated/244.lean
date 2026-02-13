

theorem closure_eq_closure_interior_of_open_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (A ∪ B : Set X) = closure (interior (A ∪ B : Set X)) := by
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B : Set X) := hA.union hB
  -- Apply the existing lemma for open sets to the union.
  simpa using
    (Topology.closure_eq_closure_interior_of_open
      (A := A ∪ B) hOpenUnion)