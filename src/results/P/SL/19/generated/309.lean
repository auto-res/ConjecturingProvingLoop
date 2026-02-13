

theorem Topology.P3_mono {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    Topology.P3 (A := A) → A ⊆ interior (closure B) := by
  intro hP3
  dsimp [Topology.P3] at hP3
  intro x hxA
  -- Step 1: `x ∈ interior (closure A)` by `P3` for `A`.
  have hxIntClosA : x ∈ interior (closure A) := hP3 hxA
  -- Step 2: Use monotonicity of `closure` and `interior` with `A ⊆ B`.
  have hClos : closure A ⊆ closure B := closure_mono hAB
  have hIntMono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono hClos
  -- Step 3: Conclude the desired membership.
  exact hIntMono hxIntClosA