

theorem Topology.P3_implies_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (A := A) → Topology.P1 (A := closure A) := by
  intro hP3
  dsimp [Topology.P1, Topology.P3] at *
  intro x hx
  -- From `hP3`, we have `A ⊆ interior (closure A)`.
  have hSub : (A : Set X) ⊆ interior (closure A) := hP3
  -- Taking closures on both sides yields
  -- `closure A ⊆ closure (interior (closure A))`.
  have hClos : closure A ⊆ closure (interior (closure A)) :=
    closure_mono hSub
  exact hClos hx