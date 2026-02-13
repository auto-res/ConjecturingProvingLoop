

theorem P2_inter_of_isClosed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hA_P2 : Topology.P2 (A : Set X)) (hB_P2 : Topology.P2 (B : Set X)) :
    Topology.P2 (A ∩ B) := by
  -- A and B are closed and satisfy `P2`, hence they are open.
  have hA_open : IsOpen (A : Set X) :=
    isOpen_of_isClosed_and_P2 (A := A) hA_closed hA_P2
  have hB_open : IsOpen (B : Set X) :=
    isOpen_of_isClosed_and_P2 (A := B) hB_closed hB_P2
  -- The intersection of two open sets is open.
  have hOpen : IsOpen (A ∩ B : Set X) := hA_open.inter hB_open
  -- An open set automatically satisfies `P2`.
  simpa using Topology.P2_of_isOpen (A := A ∩ B) hOpen