

theorem closure_eq_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P2 (X := X) A) :
    closure (A : Set X) = closure (interior A) := by
  have h₁ : closure (A : Set X) ⊆ closure (interior A) :=
    Topology.P2_closure_subset (X := X) (A := A) hA
  have h₂ : closure (interior A) ⊆ closure A :=
    Topology.closure_interior_subset_closure (X := X) A
  exact le_antisymm h₁ h₂