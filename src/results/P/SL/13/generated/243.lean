

theorem Topology.P2_closureInterior_iff_P3_closureInterior {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P2 (X := X) (closure (interior (A : Set X))) ↔
      Topology.P3 (X := X) (closure (interior (A : Set X))) := by
  -- Both sides are equivalent to the openness of `closure (interior A)`.
  have hP2 :=
    Topology.P2_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  have hP3 :=
    Topology.P3_closureInterior_iff_isOpen_closureInterior (X := X) (A := A)
  simpa using hP2.trans hP3.symm