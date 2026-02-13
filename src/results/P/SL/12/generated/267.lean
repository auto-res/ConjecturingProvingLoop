

theorem Topology.P1_closure_union_closure {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA : Topology.P1 (X := X) A) (hB : Topology.P1 (X := X) B) :
    Topology.P1 (X := X) (closure A ∪ closure B) := by
  -- Step 1: `P1` holds for `A ∪ B`.
  have hUnion : Topology.P1 (X := X) (A ∪ B) :=
    Topology.P1_union (X := X) (A := A) (B := B) hA hB
  -- Step 2: upgrade to `P1` for the closure of the union.
  have hClosureUnion : Topology.P1 (X := X) (closure (A ∪ B)) :=
    Topology.P1_closure_of_P1 (X := X) (A := A ∪ B) hUnion
  -- Step 3: identify the goal set via `closure_union`.
  have h_eq :
      (closure (A ∪ B : Set X)) =
        closure (A : Set X) ∪ closure (B : Set X) := by
    simpa [closure_union]
  -- Step 4: unfold the goal and transport memberships through the equality.
  dsimp [Topology.P1] at hClosureUnion ⊢
  intro x hx
  -- Convert membership in `closure A ∪ closure B` to membership in `closure (A ∪ B)`.
  have hx_closure : x ∈ closure (A ∪ B : Set X) := by
    have : x ∈ (closure (A : Set X) ∪ closure (B : Set X)) := hx
    simpa [h_eq] using this
  -- Apply `P1` for `closure (A ∪ B)`.
  have hx_goal :
      x ∈ closure (interior (closure (A ∪ B : Set X))) :=
    hClosureUnion hx_closure
  -- Rewrite the target set back to the desired one.
  have h_int_eq :
      interior (closure (A ∪ B : Set X)) =
        interior (closure (A : Set X) ∪ closure (B : Set X)) := by
    simpa [h_eq]
  simpa [h_int_eq] using hx_goal