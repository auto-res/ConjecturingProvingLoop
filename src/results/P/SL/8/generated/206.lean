

theorem P2_subset_closureInterior_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP2 : Topology.P2 A) (hcl : closure A ⊆ B) :
    A ⊆ closure (interior B) := by
  -- First, upgrade `P2 A` to `P1 A`.
  have hP1 : Topology.P1 A :=
    Topology.P2_imp_P1 (X := X) (A := A) hP2
  -- Then apply the existing lemma for `P1`.
  exact
    Topology.P1_subset_closureInterior_of_closure_subset
      (X := X) (A := A) (B := B) hP1 hcl