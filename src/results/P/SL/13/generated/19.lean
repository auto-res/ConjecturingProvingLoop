

theorem Topology.P3_implies_closure_eq_closureInteriorClosure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X:=X) A → closure (A : Set X) = closure (interior (closure A)) := by
  intro hP3
  apply Set.Subset.antisymm
  ·
    have : closure (A : Set X) ⊆ closure (interior (closure A)) :=
      closure_mono (hP3 : (A : Set X) ⊆ interior (closure A))
    simpa using this
  ·
    have : closure (interior (closure A)) ⊆ closure (closure (A : Set X)) :=
      closure_mono (interior_subset : interior (closure A) ⊆ closure A)
    simpa [closure_closure] using this