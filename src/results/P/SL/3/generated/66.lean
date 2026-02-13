

theorem closure_interior_eq_of_isClosed_and_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP1 : Topology.P1 (A : Set X)) :
    closure (interior (A : Set X)) = A := by
  apply Set.Subset.antisymm
  · -- `closure (interior A) ⊆ A`
    have h : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset (s := A))
    simpa [hA_closed.closure_eq] using h
  · -- `A ⊆ closure (interior A)` follows from `P1`
    exact hP1