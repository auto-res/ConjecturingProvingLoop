

theorem P1_imp_eq_empty_of_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 A) (hInt : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- From `hInt` we immediately deduce that `closure (interior A)` is empty.
  have hClInt : closure (interior A) = (∅ : Set X) := by
    simpa [hInt, closure_empty]
  -- Apply the existing lemma formulated in terms of the closure of the interior.
  exact
    P1_imp_eq_empty_of_closureInterior_empty (X := X) (A := A) hP1 hClInt