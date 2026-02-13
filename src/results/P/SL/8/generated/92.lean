

theorem P2_subset_interior_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hcl : closure A ⊆ B) :
    A ⊆ interior B := by
  -- First, upgrade `P2 A` to `P3 A`.
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Now apply the existing lemma for `P3`.
  exact
    Topology.P3_subset_interior_of_closure_subset
      (X := X) (A := A) (B := B) hP3 hcl