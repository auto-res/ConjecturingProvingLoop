

theorem P1_closure_union {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 A) (hB : Topology.P1 B) :
    Topology.P1 (closure A ∪ closure B) := by
  -- First, lift `P1` from `A` and `B` to their closures.
  have hA_cl : Topology.P1 (closure A) :=
    Topology.P1_imp_P1_closure (X := X) (A := A) hA
  have hB_cl : Topology.P1 (closure B) :=
    Topology.P1_imp_P1_closure (X := X) (A := B) hB
  -- Apply the existing union lemma for `P1`.
  exact
    Topology.P1_union (X := X) (A := closure A) (B := closure B) hA_cl hB_cl