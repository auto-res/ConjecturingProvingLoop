

theorem P2_closure_imp_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (closure A)) :
    Topology.P3 A := by
  -- First, convert `P2 (closure A)` into `P3 (closure A)` using the closed‐set equivalence.
  have hP3_closure : Topology.P3 (closure A) :=
    (Topology.P3_closure_iff_P2_closure (X := X) (A := A)).mpr hP2
  -- Then, propagate `P3` from `closure A` back to `A`.
  exact Topology.P3_closure_imp_P3 (X := X) (A := A) hP3_closure