

theorem P1_iff_P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h_dense : Dense (interior A)) : Topology.P1 (A := A) ↔ Topology.P2 (A := A) := by
  constructor
  · intro hP1
    -- From the density of `interior A` we obtain `P3 A`
    have hP3 : P3 (A := A) := P3_of_dense_interior (A := A) h_dense
    -- Combine `P1` and `P3` to get `P2`
    exact P1_and_P3_imp_P2 (A := A) hP1 hP3
  · intro hP2
    -- `P2` always implies `P1`
    exact P2_imp_P1 (A := A) hP2