

theorem Topology.P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : Topology.P2 (X := X) (closure A)) :
    Topology.P3 (X := X) A := by
  -- First, convert `P2 (closure A)` to `P3 (closure A)`.
  have hP3Closure : Topology.P3 (X := X) (closure A) :=
    (Topology.P2_closure_iff_P3_closure (X := X) (A := A)).1 h
  -- Then, descend from `closure A` to `A`.
  exact Topology.P3_of_P3_closure (X := X) (A := A) hP3Closure