

theorem Topology.P2_interior_inter
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P2 (interior A ∩ interior B) := by
  -- `interior A` and `interior B` are open, so their intersection is open.
  have hOpen : IsOpen (interior A ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  -- Any open set satisfies `P2`.
  exact Topology.P2_of_isOpen (A := interior A ∩ interior B) hOpen