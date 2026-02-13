

theorem P1_closure_interior_union {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior (A : Set X)) ∪ closure (interior (B : Set X))) := by
  -- `P1` holds for each `closure (interior A)` and `closure (interior B)`.
  have hA : Topology.P1 (closure (interior (A : Set X))) :=
    Topology.closure_interior_has_P1 (X := X) (A := A)
  have hB : Topology.P1 (closure (interior (B : Set X))) :=
    Topology.closure_interior_has_P1 (X := X) (A := B)
  -- Combine the two sets using the existing union lemma for `P1`.
  exact
    Topology.P1_union
      (X := X)
      (A := closure (interior (A : Set X)))
      (B := closure (interior (B : Set X)))
      hA hB