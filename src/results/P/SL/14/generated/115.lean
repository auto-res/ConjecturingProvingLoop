

theorem Topology.P3_of_subset_interiorClosure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : (A : Set X) ⊆ B)
    (hBsubset : (B : Set X) ⊆ interior (closure A)) :
    Topology.P3 B := by
  dsimp [Topology.P3] at *
  intro x hxB
  -- From the assumption, `x` lies in `interior (closure A)`.
  have hx_intA : (x : X) ∈ interior (closure A) := hBsubset hxB
  -- Since `A ⊆ B`, we have `closure A ⊆ closure B`.
  have h_closure_mono : closure A ⊆ closure B := closure_mono hAB
  -- Taking interiors preserves this inclusion.
  have h_int_mono : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure_mono
  -- Combining the facts gives the desired result.
  exact h_int_mono hx_intA