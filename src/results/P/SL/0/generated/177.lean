

theorem P3_mono {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P3 A → (A : Set X) ⊆ B →
      (A : Set X) ⊆ interior (closure (B : Set X)) := by
  intro hP3 hAB
  dsimp [Topology.P3] at hP3
  intro x hxA
  -- Via `P3`, `x` lies in `interior (closure A)`.
  have hx_intA : x ∈ interior (closure (A : Set X)) := hP3 hxA
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_cl : closure (A : Set X) ⊆ closure (B : Set X) := closure_mono hAB
  -- Applying monotonicity of `interior` to the previous inclusion.
  have h_mono : interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) :=
    interior_mono h_cl
  exact h_mono hx_intA