

theorem P2_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 (closure (A : Set X)) → Topology.P3 A := by
  intro hP2
  -- `closure A` is closed, so we can turn `P2` into openness.
  have hOpen : IsOpen (closure (A : Set X)) :=
    ((Topology.P2_iff_open_of_closed
        (A := closure (A : Set X)) isClosed_closure).1 hP2)
  -- Use that `interior (closure A)` equals `closure A` for an open set.
  dsimp [Topology.P3]
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  simpa [hOpen.interior_eq] using hSub