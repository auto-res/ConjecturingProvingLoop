

theorem P1_iUnion_closure {X ι : Type*} [TopologicalSpace X] {F : ι → Set X}
    (hF : ∀ i, Topology.P1 (F i)) :
    Topology.P1 (⋃ i, closure (F i : Set X)) := by
  -- Each `closure (F i)` inherits `P1` from `F i`.
  have hF_cl : ∀ i, Topology.P1 (closure (F i : Set X)) := by
    intro i
    exact Topology.P1_implies_P1_closure (X := X) (A := F i) (hF i)
  -- Apply the existing `iUnion` lemma to the family of closures.
  have h :=
    Topology.P1_iUnion (X := X)
      (F := fun i ↦ closure (F i : Set X)) hF_cl
  simpa using h