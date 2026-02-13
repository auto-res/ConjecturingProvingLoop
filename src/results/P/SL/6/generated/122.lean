

theorem closure_interior_union_satisfies_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (closure (interior (A : Set X)) ∪ closure (interior B)) := by
  -- Each of the two sets `closure (interior A)` and `closure (interior B)` satisfies `P1`.
  have hA : Topology.P1 (closure (interior (A : Set X))) :=
    Topology.closure_interior_satisfies_P1 (A := A)
  have hB : Topology.P1 (closure (interior (B : Set X))) :=
    Topology.closure_interior_satisfies_P1 (A := B)
  -- `P1` is stable under finite unions, so their union also satisfies `P1`.
  exact
    Topology.P1_union_of_P1
      (A := closure (interior (A : Set X)))
      (B := closure (interior B))
      hA hB