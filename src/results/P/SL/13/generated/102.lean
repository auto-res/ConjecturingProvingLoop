

theorem Topology.P2_inter_of_closed {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed (A : Set X)) (hB_closed : IsClosed (B : Set X))
    (hPA : Topology.P2 (X:=X) A) (hPB : Topology.P2 (X:=X) B) :
    Topology.P2 (X:=X) (A ∩ B) := by
  -- `A` is open because it is closed and satisfies `P2`
  have hA_open : IsOpen (A : Set X) := by
    have h_eq : interior (A : Set X) = A :=
      Topology.closed_P2_implies_interior_eq_self (X:=X) (A:=A) hA_closed hPA
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (A : Set X)))
  -- `B` is open for the same reason
  have hB_open : IsOpen (B : Set X) := by
    have h_eq : interior (B : Set X) = B :=
      Topology.closed_P2_implies_interior_eq_self (X:=X) (A:=B) hB_closed hPB
    simpa [h_eq] using (isOpen_interior : IsOpen (interior (B : Set X)))
  -- The intersection of two open sets is open
  have h_open : IsOpen ((A ∩ B) : Set X) := hA_open.inter hB_open
  -- Any open set satisfies `P2`
  exact isOpen_implies_P2 (X:=X) (A:=A ∩ B) h_open