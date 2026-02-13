

theorem Topology.interior_compl_eq_self_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    interior (Aᶜ) = Aᶜ := by
  have h := Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [hA.closure_eq] using h