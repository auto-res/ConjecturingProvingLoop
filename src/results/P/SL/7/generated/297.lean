

theorem Topology.P1_closure_of_dense_interiorClosure {X : Type*} [TopologicalSpace X]
    {A : Set X}
    (h : closure (interior (closure (A : Set X))) = (Set.univ : Set X)) :
    Topology.P1 (closure (A : Set X)) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure (A : Set X))) := by
    -- Since this set is the whole space, every point belongs to it.
    have : (x : X) ∈ (Set.univ : Set X) := by
      trivial
    simpa [h] using this
  simpa [closure_closure] using this