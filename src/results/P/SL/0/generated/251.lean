

theorem closure_subset_closure_interior_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → closure (A : Set X) ⊆ closure (interior A) := by
  intro hP2
  -- First, derive an inclusion involving a more complicated target set.
  have hSub :=
    Topology.P2_implies_closure_subset_closure_interior_closure_interior
      (X := X) (A := A) hP2
  -- Simplify the target set using the idempotence lemma.
  have hId :
      closure (interior (closure (interior (A : Set X)))) =
        closure (interior (A : Set X)) :=
    Topology.closure_interior_closure_interior_idempotent (X := X) (A := A)
  -- Rewriting with `hId` yields the desired inclusion.
  simpa [hId] using hSub