

theorem Topology.interior_compl_eq_empty_of_dense {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    closure A = (Set.univ : Set X) → interior (Aᶜ) = (∅ : Set X) := by
  intro h_dense
  have h_eq : interior (Aᶜ) = (closure A)ᶜ :=
    Topology.interior_compl_eq_compl_closure (X := X) (A := A)
  simpa [h_dense] using h_eq