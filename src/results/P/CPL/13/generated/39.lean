

theorem P2_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P2 A) (hB : Topology.P2 B) : Topology.P2 (Set.prod (interior A) (interior B)) := by
  -- The interiors of `A` and `B` satisfy `P2`.
  have hA_int : Topology.P2 (interior A) := by
    simpa using (Topology.P2_interior (A := A))
  have hB_int : Topology.P2 (interior B) := by
    simpa using (Topology.P2_interior (A := B))
  -- Apply the product theorem for `P2`.
  simpa using
    (Topology.P2_prod (A := interior A) (B := interior B) hA_int hB_int)