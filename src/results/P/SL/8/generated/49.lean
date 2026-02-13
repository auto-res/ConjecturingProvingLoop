

theorem P2_subset_interiorClosure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP2 : Topology.P2 A) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  -- Upgrade `P2` to `P3`
  have hP3 : Topology.P3 A :=
    Topology.P2_imp_P3 (X := X) (A := A) hP2
  -- Use the existing lemma for `P3`
  exact
    Topology.P3_subset_interiorClosure_of_subset (X := X) (A := A) (B := B) hP3 hAB