

theorem Topology.closure_eq_closureInteriorClosure_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    closure (A : Set X) = closure (interior (closure (A : Set X))) := by
  apply Set.Subset.antisymm
  ·
    have hSub : (A : Set X) ⊆ interior (closure (A : Set X)) := hP3
    simpa using (closure_mono hSub)
  ·
    have hSub : (interior (closure (A : Set X)) : Set X) ⊆ closure (A : Set X) :=
      interior_subset
    simpa using (closure_mono hSub)