

theorem interior_union_eq_of_open
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    interior ((A ∪ B) : Set X) = interior A ∪ interior B := by
  -- The interiors of open sets coincide with the sets themselves.
  have hIntA : interior (A : Set X) = A := hA.interior_eq
  have hIntB : interior (B : Set X) = B := hB.interior_eq
  -- The union of two open sets is open, hence its interior is itself.
  have hIntUnion : interior (A ∪ B : Set X) = A ∪ B :=
    (hA.union hB).interior_eq
  simpa [hIntA, hIntB, hIntUnion]