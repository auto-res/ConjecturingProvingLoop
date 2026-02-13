

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense (interior (A : Set X)) → Topology.P2 A := by
  intro hDenseInt
  -- From density, obtain `interior (closure (interior A)) = univ`.
  have hUniv :
      interior (closure (interior (A : Set X))) = (Set.univ : Set X) :=
    (Topology.dense_interior_iff_interior_closure_interior_eq_univ
        (A := A)).1 hDenseInt
  -- Unfold `P2` and finish the proof.
  dsimp [Topology.P2]
  intro x _hxA
  have hx_univ : (x : X) ∈ (Set.univ : Set X) := by
    trivial
  simpa [hUniv] using hx_univ