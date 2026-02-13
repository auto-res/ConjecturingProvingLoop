

theorem boundary_interior_eq_closure_inter_complement
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (A : Set X)) \ interior (A : Set X) =
      closure (interior (A : Set X)) ∩
        closure ((interior (A : Set X))ᶜ) := by
  simpa using
    (boundary_of_isOpen (A := interior (A : Set X)) isOpen_interior)