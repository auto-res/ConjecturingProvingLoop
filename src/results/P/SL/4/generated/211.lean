

theorem closure_interior_closure_interior_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (interior (closure (interior A))) ⊆
      closure (interior (closure A)) := by
  have h :
      interior (closure (interior A)) ⊆ interior (closure A) :=
    Topology.interior_closure_interior_subset_interior_closure
      (X := X) (A := A)
  exact closure_mono h