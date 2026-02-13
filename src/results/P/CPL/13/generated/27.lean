

theorem P1_uniform_isOpen {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 (closure A) := by
  intro h_open
  exact Topology.P1_closure (A := A) (Topology.P1_of_open (A := A) h_open)