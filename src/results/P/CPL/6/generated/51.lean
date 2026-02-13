

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] : Topology.P2 ((Set.univ : Set X) ×ˢ (Set.univ : Set Y)) := by
  intro x hx
  simpa [interior_univ, closure_univ] using (Set.mem_univ (x : X × Y))