

theorem P2_imp_eq_empty_of_interior_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 A) (hInt : interior A = (∅ : Set X)) :
    A = (∅ : Set X) := by
  -- From `interior A = ∅`, deduce `closure (interior A) = ∅`.
  have hClInt : closure (interior A) = (∅ : Set X) := by
    simpa [hInt] using (closure_empty : closure (∅ : Set X) = ∅)
  -- Apply the existing lemma formulated in terms of `closure (interior A)`.
  exact
    P2_imp_eq_empty_of_closureInterior_empty (X := X) (A := A) hP2 hClInt