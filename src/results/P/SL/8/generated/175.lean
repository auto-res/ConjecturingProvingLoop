

theorem closureInterior_union_eq_union_closureInterior_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  -- Since `A` and `B` are open, so is their union, and the `interior`
  -- of an open set is itself.
  have h_union_open : IsOpen (A ∪ B) := hA.union hB
  simpa [h_union_open.interior_eq, hA.interior_eq, hB.interior_eq] using
    (closure_union : closure (A ∪ B) = closure A ∪ closure B)