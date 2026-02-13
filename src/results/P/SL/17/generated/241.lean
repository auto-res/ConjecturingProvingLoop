

theorem Topology.interior_union_eq_union_interior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  -- For open sets, the interior coincides with the set itself.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- Likewise, `A ∪ B` is open, so its interior is itself.
  have hIntUnion : interior (A ∪ B) = A ∪ B :=
    Topology.interior_union_eq_of_isOpen (A := A) (B := B) hA hB
  -- Rewrite each interior using the equalities above and simplify.
  simpa [hIntA, hIntB, hIntUnion]