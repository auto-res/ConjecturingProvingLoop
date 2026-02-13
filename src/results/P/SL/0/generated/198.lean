

theorem iUnion_open_has_all_Ps {X ι : Type*} [TopologicalSpace X] {F : ι → Set X}
    (hF : ∀ i, IsOpen (F i : Set X)) :
    Topology.P1 (⋃ i, F i) ∧ Topology.P2 (⋃ i, F i) ∧ Topology.P3 (⋃ i, F i) := by
  have hOpen : IsOpen (⋃ i, F i : Set X) := isOpen_iUnion (fun i ↦ hF i)
  exact Topology.isOpen_has_all_Ps (X := X) (A := (⋃ i, F i : Set X)) hOpen