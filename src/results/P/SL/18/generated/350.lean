

theorem interior_eq_empty_iff_closure_complement_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (A : Set X) = ∅ ↔ closure (Aᶜ : Set X) = (Set.univ : Set X) := by
  classical
  have h₁ :=
    (Topology.dense_compl_iff_interior_eq_empty (A := A)).symm
  have h₂ :=
    (Topology.dense_iff_closure_eq_univ (A := (Aᶜ : Set X)))
  simpa using h₁.trans h₂