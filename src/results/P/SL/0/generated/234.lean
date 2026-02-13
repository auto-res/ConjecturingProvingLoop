

theorem P2_implies_P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → Topology.P3 (interior (A : Set X)) := by
  intro hP2
  -- Step 1: `P2` propagates from `A` to its interior.
  have hP2_int : Topology.P2 (interior (A : Set X)) :=
    (Topology.P2_implies_P2_interior (X := X) (A := A)) hP2
  -- Step 2: For the open set `interior A`, `P2` and `P3` are equivalent.
  have hEquiv :=
    (Topology.P2_iff_P3_of_interior (X := X) (A := A))
  -- Step 3: Convert `P2` into `P3` via the equivalence.
  exact (hEquiv).1 hP2_int