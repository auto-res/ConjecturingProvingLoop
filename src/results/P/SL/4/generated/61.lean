

theorem dense_imp_P2_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Dense A → Topology.P2 (closure A) := by
  intro hDense
  dsimp [Topology.P2]
  intro x hx_cl
  -- `closure A` is closed.
  have hClosed : IsClosed (closure A) := isClosed_closure
  -- For a closed set, `interior (closure (interior C)) = interior C`.
  have h_int_eq :
      interior (closure (interior (closure A))) = interior (closure A) :=
    interior_closure_interior_eq_interior_of_closed
      (X := X) (A := closure A) hClosed
  -- Since `A` is dense, `closure A = univ`.
  have h_closure_univ : (closure A : Set X) = Set.univ := hDense.closure_eq
  -- Hence `interior (closure A) = univ`.
  have h_int_univ : interior (closure A) = (Set.univ : Set X) := by
    have : interior (Set.univ : Set X) = (Set.univ : Set X) := by
      simpa using (isOpen_univ : IsOpen (Set.univ : Set X)).interior_eq
    simpa [h_closure_univ] using this
  -- Combining the two equalities, the target interior is `univ`.
  have h_target :
      interior (closure (interior (closure A))) = (Set.univ : Set X) := by
    simpa [h_int_univ] using h_int_eq
  -- Any point belongs to `univ`, so we are done.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_target] using this