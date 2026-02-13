

theorem interior_union_eq_union_interiors_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    interior (A ∪ B) = interior A ∪ interior B := by
  -- `A` and `B` are open, so their interiors coincide with themselves.
  have hIntA : interior A = A := hA.interior_eq
  have hIntB : interior B = B := hB.interior_eq
  -- The union of two open sets is open.
  have hOpenUnion : IsOpen (A ∪ B) := hA.union hB
  -- Hence the interior of the union is the union itself.
  have hIntUnion : interior (A ∪ B) = A ∪ B := hOpenUnion.interior_eq
  -- Rewrite everything in terms of `interior`.
  simpa [hIntUnion, hIntA, hIntB]