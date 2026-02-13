

theorem interior_inter_has_all_Ps {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior ((A ∩ B) : Set X)) ∧
    Topology.P2 (interior ((A ∩ B) : Set X)) ∧
    Topology.P3 (interior ((A ∩ B) : Set X)) := by
  -- The set `interior (A ∩ B)` is open.
  have hOpen : IsOpen (interior ((A ∩ B) : Set X)) := isOpen_interior
  -- Every open set satisfies all three properties.
  exact
    Topology.isOpen_has_all_Ps
      (X := X) (A := interior (A ∩ B : Set X)) hOpen