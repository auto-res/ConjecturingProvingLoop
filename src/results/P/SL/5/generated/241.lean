

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X}
    (h : interior (A : Set X) = Set.univ) :
    Topology.P1 (X := X) A ↔ Topology.P2 (X := X) A := by
  -- Both properties hold unconditionally under the dense‐interior hypothesis.
  have hP1 : Topology.P1 (X := X) A :=
    Topology.P1_of_dense_interior (X := X) (A := A) h
  have hP2 : Topology.P2 (X := X) A :=
    Topology.P2_of_dense_interior (X := X) (A := A) h
  exact ⟨fun _ => hP2, fun _ => hP1⟩