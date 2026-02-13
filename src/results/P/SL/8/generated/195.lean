

theorem P2_subset_closureInterior_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- Upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Use the existing lemma for `P1`.
  exact
    Topology.P1_subset_closureInterior_of_subset
      (X := X) (A := A) (B := B) hP1 hAB