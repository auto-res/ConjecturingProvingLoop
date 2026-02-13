

theorem P1_inter_four_of_open {X : Type*} [TopologicalSpace X]
    {A B C D : Set X} (hA : IsOpen (A : Set X)) (hB : IsOpen (B : Set X))
    (hC : IsOpen (C : Set X)) (hD : IsOpen (D : Set X)) :
    Topology.P1 (A ∩ B ∩ C ∩ D) := by
  -- The intersection of four open sets is open.
  have hOpen : IsOpen ((A ∩ B ∩ C ∩ D) : Set X) :=
    (((hA.inter hB).inter hC).inter hD)
  -- Every open set satisfies `P1`.
  exact
    (Topology.isOpen_has_all_Ps
        (X := X)
        (A := (A ∩ B ∩ C ∩ D : Set X))
        hOpen).1