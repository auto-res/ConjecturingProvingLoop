

theorem closure_eq_closure_interior_closure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    closure A = closure (interior (closure A)) := by
  apply Set.Subset.antisymm
  ·
    have hSub : (A : Set X) ⊆ interior (closure A) := hP3
    simpa using (closure_mono hSub)
  ·
    have hSub : interior (closure A) ⊆ closure A := interior_subset
    have : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono hSub
    simpa [closure_closure] using this