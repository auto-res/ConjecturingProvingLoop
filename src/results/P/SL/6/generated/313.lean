

theorem interior_union_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] (A B : Set X) :
    Topology.P1 (interior A ∪ interior B) ∧
      Topology.P2 (interior A ∪ interior B) ∧
      Topology.P3 (interior A ∪ interior B) := by
  -- The interiors of any sets are open.
  have hOpenA : IsOpen (interior A) := isOpen_interior
  have hOpenB : IsOpen (interior B) := isOpen_interior
  -- Apply the existing lemma for unions of open sets.
  simpa using
    (Topology.open_union_satisfies_all_Ps
      (A := interior A) (B := interior B) hOpenA hOpenB)