

theorem P2_iff_P3_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P2 A ↔ P3 A := by
  -- Since `A` is closed we have `closure A = A`.
  have hClosure : (closure (A : Set X)) = A := hA.closure_eq
  constructor
  · -- First direction:  `P2 A → P3 A`
    intro hP2
    -- Unfold `P3`
    intro x hxA
    -- Use `P2` to put `x` in the open set `interior (closure (interior A))`.
    have hx₁ : x ∈ interior (closure (interior A)) := hP2 hxA
    -- Because `A` is closed, `closure (interior A) ⊆ A`.
    have hSub : (closure (interior A) : Set X) ⊆ A :=
      closure_minimal (interior_subset : (interior A : Set X) ⊆ A) hA
    -- Hence the interiors satisfy the same inclusion.
    have hIntSub :
        (interior (closure (interior A)) : Set X) ⊆ interior A :=
      interior_mono hSub
    -- Place `x` in `interior A`, then rewrite using `closure A = A`.
    have hxIntA : x ∈ interior A := hIntSub hx₁
    simpa [hClosure] using hxIntA
  · -- Second direction:  `P3 A → P2 A`
    intro hP3
    -- First prove that `A` is open.
    have hOpenA : IsOpen (A : Set X) := by
      -- Show `interior A = A`.
      have hEq : interior A = A := by
        apply Set.Subset.antisymm interior_subset
        intro x hxA
        have hxIntCl : x ∈ interior (closure A) := hP3 hxA
        simpa [hClosure] using hxIntCl
      simpa [hEq] using (isOpen_interior : IsOpen (interior A))
    -- On an open set, `P2` holds by `P2_of_open`.
    exact P2_of_open (A := A) hOpenA

theorem exists_P1_compact_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ K, K ⊆ A ∧ IsCompact K ∧ P1 K := by
  refine ⟨(∅ : Set X), Set.empty_subset _, isCompact_empty, P1_empty⟩