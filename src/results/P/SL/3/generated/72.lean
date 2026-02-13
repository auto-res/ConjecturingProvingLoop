

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2
  dsimp [Topology.P3]
  intro x hxA
  -- `x` is in `closure A`
  have hxClosure : (x : X) ∈ closure (A : Set X) := subset_closure hxA
  -- Apply `P2` for `closure A`
  have hxInt₁ :
      (x : X) ∈ interior (closure (interior (closure (A : Set X)))) :=
    hP2 hxClosure
  -- Use the inclusion
  have hSubset :
      interior (closure (interior (closure (A : Set X)))) ⊆
        interior (closure (A : Set X)) := by
    simpa using
      (interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
  exact hSubset hxInt₁