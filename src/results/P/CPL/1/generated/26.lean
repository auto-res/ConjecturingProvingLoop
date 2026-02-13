

theorem P1_Union_four {X : Type*} [TopologicalSpace X] {A B C D : Set X} (hA : P1 A) (hB : P1 B) (hC : P1 C) (hD : P1 D) : P1 (A ∪ B ∪ C ∪ D) := by
  -- Step 1: obtain `P1` for `A ∪ B`
  have hAB : P1 (A ∪ B) :=
    P1_union (A := A) (B := B) hA hB
  -- Step 2: obtain `P1` for `A ∪ B ∪ C`
  have hABC : P1 (A ∪ B ∪ C) := by
    have : P1 ((A ∪ B) ∪ C) :=
      P1_union (A := (A ∪ B)) (B := C) hAB hC
    simpa [Set.union_assoc] using this
  -- Step 3: obtain `P1` for `A ∪ B ∪ C ∪ D`
  have hABCD : P1 (A ∪ B ∪ C ∪ D) := by
    have : P1 ((A ∪ B ∪ C) ∪ D) :=
      P1_union (A := (A ∪ B ∪ C)) (B := D) hABC hD
    simpa [Set.union_assoc] using this
  exact hABCD

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (e : X ≃ₜ Y) (hA : P3 A) : P3 (e '' A) := by
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` lies in the interior of `closure A`
  have hx_int : (x : X) ∈ interior (closure A) := hA hxA
  -- Transport through the homeomorphism
  have h1 : (e x) ∈ interior (e '' closure A : Set Y) := by
    -- first as an element of `e '' interior (closure A)`
    have hmem : (e x) ∈ (e '' interior (closure A) : Set Y) :=
      ⟨x, hx_int, rfl⟩
    simpa [e.image_interior (s := closure A)] using hmem
  -- Rewrite the image of the closure
  have h2 : (e x) ∈ interior (closure (e '' A : Set Y)) := by
    simpa [e.image_closure (s := A)] using h1
  exact h2