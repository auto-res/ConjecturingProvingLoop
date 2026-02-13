

theorem P2_prod_interior_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (Set.prod (interior A) (Set.univ : Set Y)) := by
  -- The interior of `A` satisfies `P2`.
  have h_int : Topology.P2 (interior A) := by
    simpa using (Topology.P2_interior (A := A))
  -- Apply the `P2_prod_univ` theorem with `interior A`.
  simpa using
    (Topology.P2_prod_univ (X := X) (Y := Y) (A := interior A) h_int)

theorem P3_prod_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P3 A) (hB : Topology.P3 B) : Topology.P3 (Set.prod (interior A) (interior B)) := by
  -- The interiors of `A` and `B` satisfy `P3`.
  have hA_int : Topology.P3 (interior A) := by
    simpa using (Topology.P3_interior (A := A))
  have hB_int : Topology.P3 (interior B) := by
    simpa using (Topology.P3_interior (A := B))
  -- Apply the product theorem for `P3`.
  simpa using
    (Topology.P3_prod (A := interior A) (B := interior B) hA_int hB_int)