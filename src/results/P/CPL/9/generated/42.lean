

theorem P3_of_closed_ball {X : Type*} [MetricSpace X] {x : X} {r : ℝ} : Topology.P3 (A := Metric.ball x r) := by
  apply Topology.P3_of_open
  simpa using isOpen_ball

theorem P2_iterate_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (A := interior (interior A)) := by
  apply P2_of_open
  simpa using isOpen_interior