

theorem P2_union_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∪ B ∪ C) := by
  -- First, obtain `P2` for `A ∪ B`.
  have hAB : Topology.P2 (A ∪ B) :=
    Topology.P2_union (X := X) (A := A) (B := B) hA hB
  -- Combine with `C`.
  simpa using
    (Topology.P2_union (X := X) (A := A ∪ B) (B := C) hAB hC)

theorem P3_closed_iff {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ interior A = A := by
  -- First, record that the closure of `A` is `A` itself.
  have h_closure : closure (A : Set X) = A := hA.closure_eq
  -- Establish the desired equivalence.
  constructor
  · -- `P3 A → interior A = A`
    intro hP3
    apply le_antisymm
    · -- `interior A ⊆ A`
      exact interior_subset
    · -- `A ⊆ interior A`
      have : (A : Set X) ⊆ interior (closure A) := hP3
      simpa [h_closure] using this
  · -- `interior A = A → P3 A`
    intro hIntEq
    intro x hx
    -- From `x ∈ A` and `interior A = A` we get `x ∈ interior A`.
    have hx_int : x ∈ interior A := by
      simpa [hIntEq] using hx
    -- Rewrite `interior (closure A)` using `closure A = A`.
    simpa [h_closure] using hx_int