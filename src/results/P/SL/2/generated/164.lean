

theorem Topology.isOpen_iUnion_implies_P1 {X : Type*} [TopologicalSpace X] {ι : Type*}
    {s : ι → Set X} :
    (∀ i, IsOpen (s i)) → Topology.P1 (⋃ i, s i) := by
  intro hOpen
  have hOpenUnion : IsOpen (⋃ i, s i) := isOpen_iUnion (fun i => hOpen i)
  exact Topology.isOpen_implies_P1 (A := ⋃ i, s i) hOpenUnion