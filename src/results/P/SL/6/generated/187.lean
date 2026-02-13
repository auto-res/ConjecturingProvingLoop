

theorem iUnion_open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {ι : Sort*} {S : ι → Set X}
    (hS : ∀ i, IsOpen (S i)) :
    Topology.P1 (⋃ i, S i) ∧ Topology.P2 (⋃ i, S i) ∧ Topology.P3 (⋃ i, S i) := by
  have hOpen : IsOpen (⋃ i, S i : Set X) := by
    simpa using isOpen_iUnion (fun i => hS i)
  exact Topology.open_satisfies_all_Ps (A := ⋃ i, S i) hOpen