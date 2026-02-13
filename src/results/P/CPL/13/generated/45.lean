

theorem P1_prod_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (closure (Set.prod A B)) := by
  have hAB : Topology.P1 (Set.prod A B) := Topology.P1_prod hA hB
  simpa using (Topology.P1_closure (A := Set.prod A B) hAB)