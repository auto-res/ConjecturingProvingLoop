

theorem Topology.P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  dsimp [Topology.P1] at hP1 ⊢
  intro x hx
  -- Step 1: turn `x ∈ closure A` into `x ∈ closure (interior A)`
  have hsubset1 : closure A ⊆ closure (interior A) := by
    have htemp : closure A ⊆ closure (closure (interior A)) :=
      closure_mono hP1
    simpa [closure_closure] using htemp
  -- Step 2: upgrade to `x ∈ closure (interior (closure A))`
  have hsubset2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have htemp : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono htemp
  exact hsubset2 (hsubset1 hx)