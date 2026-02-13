

theorem Topology.closure_interior_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The union of two open sets is open.
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  -- For an open set `S`, `interior S = S`.
  have hInt : interior (A ∪ B) = A ∪ B := hOpen.interior_eq
  -- Rewrite and use the `closure_union` lemma.
  simpa [hInt, closure_union]