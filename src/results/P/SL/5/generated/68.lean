

theorem closure_eq_closure_interior_closure_of_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : Topology.P3 (X := X) A) :
    closure (A : Set X) = closure (interior (closure A)) := by
  apply le_antisymm
  ·
    exact Topology.P3_closure_subset (X := X) (A := A) hA
  ·
    have hsubset : interior (closure (A : Set X)) ⊆ closure A := interior_subset
    have hclosure_subset :
        closure (interior (closure (A : Set X))) ⊆ closure (closure A) :=
      closure_mono hsubset
    simpa [closure_closure] using hclosure_subset