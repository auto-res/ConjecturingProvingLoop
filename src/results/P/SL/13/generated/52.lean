

theorem Topology.P3_closure_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (X := X) (closure (A : Set X)) → Topology.P3 (X := X) A := by
  intro hP3cl
  dsimp [Topology.P3] at *
  intro x hx
  -- First, place `x` inside `closure A`.
  have hx_cl : (x : X) ∈ closure (A : Set X) := subset_closure hx
  -- Apply the P3 hypothesis for `closure A`.
  have hx_int : (x : X) ∈ interior (closure (closure (A : Set X))) := hP3cl hx_cl
  -- Simplify the double closure.
  simpa [closure_closure] using hx_int