

theorem Topology.interior_union_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior (A ∪ B : Set X) = interior A ∪ interior B := by
  -- Evaluate the interiors of the open sets `A` and `B`.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- The union of two open sets is open, so its interior is itself.
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  -- Rewrite everything using the computed equalities.
  simpa [hIntA, hIntB, hIntUnion]