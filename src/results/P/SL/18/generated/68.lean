

theorem P3_of_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2Clos
  dsimp [Topology.P3] at *
  intro x hxA
  -- `x` lies in the closure of `A`.
  have hxClos : x ∈ closure (A : Set X) :=
    (subset_closure : (A : Set X) ⊆ closure A) hxA
  -- Apply `P2` to `closure A`.
  have hxInt :
      x ∈ interior (closure (interior (closure (A : Set X)))) :=
    hP2Clos hxClos
  -- Relate the two interiors via the auxiliary lemma.
  have hIncl :
      interior (closure (interior (closure (A : Set X))))
        ⊆ interior (closure (A : Set X)) := by
    simpa using
      (Topology.interior_closure_interior_subset_interior_closure
        (A := closure (A : Set X)))
  exact hIncl hxInt