

theorem Topology.closureInteriorClosure_mono
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- From `A ⊆ B`, we get `closure A ⊆ closure B`.
  have h₁ : (closure A : Set X) ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves the inclusion.
  have h₂ : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h₁
  -- Taking closures once more yields the desired inclusion.
  exact closure_mono h₂