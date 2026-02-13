

theorem Topology.P1_implies_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  have h₁ : closure (interior A) ⊆ closure A := closure_mono interior_subset
  have h₂ : closure A ⊆ closure (interior A) :=
    Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  exact subset_antisymm h₁ h₂