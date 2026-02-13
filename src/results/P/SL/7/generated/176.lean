

theorem Topology.closureInterior_union_eq_closure_union {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- The set `A ∪ B` is open, so its interior is itself.
  have hOpen : IsOpen (A ∪ B) := hA.union hB
  have hInt : interior (A ∪ B) = A ∪ B := hOpen.interior_eq
  -- Distribute `closure` over the union.
  simpa [hInt, closure_union]