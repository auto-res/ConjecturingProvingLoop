

theorem Topology.P2_nonempty_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 A) (hA : A.Nonempty) :
    (interior (closure A)).Nonempty := by
  -- First upgrade `P2` to `P3`
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Then use the existing result for `P3`
  exact Topology.P3_nonempty_interiorClosure (X := X) (A := A) hP3 hA