

theorem Topology.closure_compl_eq_self_of_isOpen {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) :
    closure (Aᶜ : Set X) = Aᶜ := by
  simpa [hA.interior_eq] using
    (Topology.closure_compl_eq_compl_interior (X := X) (A := A))