

theorem Topology.closureInterior_union_eq_closure_union_of_isOpen
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X)) :
    closure (interior (A ∪ B : Set X)) = closure (A : Set X) ∪ closure B := by
  -- The union of two open sets is open.
  have hAB_open : IsOpen (A ∪ B : Set X) := IsOpen.union hA hB
  -- For an open set, its interior is itself.
  have h_int : interior (A ∪ B : Set X) = A ∪ B := by
    simpa using hAB_open.interior_eq
  -- Rewrite the left‐hand side using `h_int` and simplify with `closure_union`.
  simpa [h_int, closure_union]