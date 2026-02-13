

theorem closure_interior_union_closure_compl_interior_eq_univ
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) ∪ closure ((interior (A : Set X))ᶜ) =
      (Set.univ : Set X) := by
  simpa using
    Topology.closure_union_compl_eq_univ
      (X := X) (A := interior (A : Set X))