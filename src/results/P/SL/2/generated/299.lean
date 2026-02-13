

theorem Topology.P1_implies_frontier_closure_subset_closure_interior_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      frontier (closure (A : Set X)) ⊆
        closure (interior (closure (A : Set X))) := by
  intro hP1
  -- `P1` also holds for `closure A`.
  have hP1_closure : Topology.P1 (closure (A : Set X)) :=
    Topology.P1_closure_of_P1 (A := A) hP1
  -- Apply the frontier lemma to `closure A`.
  have hIncl :
      frontier (closure (A : Set X)) ⊆
        closure (interior (closure (closure (A : Set X)))) :=
    Topology.P1_implies_frontier_subset_closure_interior_closure
      (A := closure (A : Set X)) hP1_closure
  -- Simplify the target using idempotence of `closure`.
  simpa [closure_closure] using hIncl