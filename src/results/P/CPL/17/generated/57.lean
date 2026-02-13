

theorem P2_unionᵢ_closed {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, IsClosed (f i)) → (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, closure (f i)) := by
  intro hClosed hP2
  -- Each `closure (f i)` coincides with `f i` since `f i` is closed,
  -- hence it also satisfies `P2`.
  have hP2_closure : ∀ i, Topology.P2 (closure (f i)) := by
    intro i
    have h_eq : closure (f i) = f i := (hClosed i).closure_eq
    simpa [h_eq] using hP2 i
  -- Apply the `iUnion` lemma to the family `i ↦ closure (f i)`.
  simpa using
    (P2_iUnion (X := X) (f := fun i => closure (f i)) hP2_closure)