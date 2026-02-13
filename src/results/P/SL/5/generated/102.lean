

theorem closure_inter_interior_subset_closure_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior (A ∩ B)) := by
  have hsubset :
      (interior (A : Set X) ∩ interior B : Set X) ⊆ interior (A ∩ B) :=
    Topology.interior_interiors_subset_interior_inter (X := X) (A := A) (B := B)
  exact closure_mono hsubset