

theorem closure_interior_inter_subset_closure_interiors
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A ∩ B : Set X)) ⊆
      closure (interior (A : Set X) ∩ interior B) := by
  have h :
      (interior (A ∩ B : Set X)) ⊆ interior (A : Set X) ∩ interior B :=
    Topology.interior_inter_subset (X := X) (A := A) (B := B)
  exact closure_mono h