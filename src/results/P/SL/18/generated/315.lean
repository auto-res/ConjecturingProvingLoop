

theorem interior_closure_union_eq_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (closure (A : Set X))) (hB : IsOpen (closure B)) :
    interior (closure (A ∪ B : Set X)) = closure (A : Set X) ∪ closure B := by
  -- Rewrite the closure of the union using `closure_union`.
  have hClos : closure (A ∪ B : Set X) = closure (A : Set X) ∪ closure B := by
    simpa [closure_union]
  -- The right‐hand side is an open set (union of two open sets).
  have hOpen : IsOpen (closure (A : Set X) ∪ closure B) := hA.union hB
  -- For an open set, its interior coincides with itself.
  have hInt :
      interior (closure (A : Set X) ∪ closure B) =
        closure (A : Set X) ∪ closure B := hOpen.interior_eq
  -- Combine the two equalities.
  simpa [hClos] using hInt