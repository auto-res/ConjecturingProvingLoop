

theorem P3_implies_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → Topology.P3 (interior (A : Set X)) := by
  intro hP3
  -- Step 1:  From `P3 A`, obtain `P2 (interior A)`.
  have hP2_int : Topology.P2 (interior (A : Set X)) :=
    (Topology.P3_implies_P2_interior (X := X) (A := A)) hP3
  -- Step 2:  For the open set `interior A`, `P2` is equivalent to `P3`.
  have hEquiv :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  exact (hEquiv).1 hP2_int