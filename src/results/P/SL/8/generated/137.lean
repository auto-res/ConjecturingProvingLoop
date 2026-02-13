

theorem closureInterior_union_eq_union_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen A) (hB : IsOpen B) :
    closure (interior (A ∪ B)) = closure A ∪ closure B := by
  -- `interior` of an open set is itself.
  have h_int : interior (A ∪ B) = A ∪ B := by
    have h_open : IsOpen (A ∪ B) := hA.union hB
    simpa using h_open.interior_eq
  -- Rewrite and use the distributivity of `closure` over unions.
  calc
    closure (interior (A ∪ B)) = closure (A ∪ B) := by
      simpa [h_int]
    _ = closure A ∪ closure B := by
      simpa using
        (closure_union : closure (A ∪ B) = closure A ∪ closure B)