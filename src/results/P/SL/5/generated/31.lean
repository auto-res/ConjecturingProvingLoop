

theorem P1_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (X := X) (closure (interior A)) := by
  dsimp [Topology.P1]
  intro x hx
  -- Using idempotency of `closure ∘ interior`.
  have h_eq : closure (interior (closure (interior A))) = closure (interior A) := by
    simpa using Topology.closure_interior_idempotent (X := X) (A := interior A)
  -- Rewrite the membership with the obtained equality.
  have : x ∈ closure (interior (closure (interior A))) := by
    have hx' : x ∈ closure (interior A) := hx
    simpa [h_eq] using hx'
  exact this