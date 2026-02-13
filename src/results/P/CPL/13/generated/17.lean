

theorem P1_prod_three {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {A : Set X} {B : Set Y} {C : Set Z} (hA : Topology.P1 A) (hB : Topology.P1 B) (hC : Topology.P1 C) : Topology.P1 (Set.prod (Set.prod A B) C) := by
  have hAB : Topology.P1 (Set.prod A B) := Topology.P1_prod hA hB
  simpa using (Topology.P1_prod hAB hC)